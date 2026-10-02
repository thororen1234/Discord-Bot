const { EventEmitter } = require('events');
const { spawn } = require('child_process');
const crypto = require('crypto');
const path = require('path');
const { Transform } = require('stream');
const axios = require('axios');
const {
	AudioPlayerStatus,
	createAudioPlayer,
	createAudioResource,
	entersState,
	joinVoiceChannel,
	StreamType,
	VoiceConnectionStatus,
} = require('@discordjs/voice');
const ffmpegPath = require('ffmpeg-static');
const youtubedl = require('youtube-dl-exec');

class Queue extends Array {
	constructor() {
		super();
		this.current = null;
		this.previous = null;
	}

	get size() {
		return this.length;
	}

	get totalSize() {
		return this.length + (this.current ? 1 : 0);
	}

	add(tracks) {
		const items = [...(Array.isArray(tracks) ? tracks : [tracks])];
		if (!this.current && !this.length) this.current = items.shift() || null;
		this.push(...items);
		return this;
	}

	shuffle() {
		for (let i = this.length - 1; i > 0; i--) {
			const j = Math.floor(Math.random() * (i + 1));
			[this[i], this[j]] = [this[j], this[i]];
		}
		return this;
	}
}

const isUrl = value => /^https?:\/\//i.test(value);
const number = value => Number.isFinite(Number(value)) ? Number(value) : 0;

const EXTERNAL_SOURCES = [
	{ id: 'yandex', label: 'Yandex Music', hosts: [/(^|\.)music\.yandex\.(ru|com|kz|by|ua)$/] },
	{ id: 'vk', label: 'VK Music', hosts: [/(^|\.)vk\.com$/, /(^|\.)vkvideo\.ru$/] },
	{ id: 'qobuz', label: 'Qobuz', hosts: [/(^|\.)qobuz\.com$/] },
	{ id: 'jiosaavn', label: 'JioSaavn', hosts: [/(^|\.)jiosaavn\.com$/, /(^|\.)saavn\.com$/] },
	{ id: 'mixcloud', label: 'Mixcloud', hosts: [/(^|\.)mixcloud\.com$/] },
	{ id: 'ocremix', label: 'OC Remix', hosts: [/(^|\.)ocremix\.org$/], identifiers: [/^OCR\d+$/i] },
	{ id: 'clypit', label: 'Clyp.it', hosts: [/(^|\.)clyp\.it$/] },
	{ id: 'reddit', label: 'Reddit', hosts: [/(^|\.)reddit\.com$/, /(^|\.)redd\.it$/] },
	{ id: 'getyarn', label: 'getyarn', hosts: [/(^|\.)getyarn\.io$/, /(^|\.)yarn\.co$/] },
	{ id: 'tiktok', label: 'TikTok', hosts: [/(^|\.)tiktok\.com$/] },
	{ id: 'soundgasm', label: 'Soundgasm', hosts: [/(^|\.)soundgasm\.net$/] },
	{ id: 'pixeldrain', label: 'Pixeldrain', hosts: [/(^|\.)pixeldrain\.com$/] },
	{ id: 'tumblr', label: 'Tumblr', hosts: [/(^|\.)tumblr\.com$/] },
	{ id: 'pornhub', label: 'Pornhub', nsfw: true, hosts: [/(^|\.)pornhub\.com$/, /(^|\.)pornhubpremium\.com$/], identifiers: [/^phsearch:.+/i] },
];

const providerNames = {
	flowerytts: 'Flowery TTS',
	speechtts: 'Google TTS',
	streamdeck: 'Stream Deck audio',
	upload: 'File uploads',
	getyarn: 'getyarn',
	jiosaavn: 'JioSaavn',
	ocremix: 'OC Remix',
	soundgasm: 'Soundgasm',
	appmusic: 'Apple Music',
};

function getExternalSource(input) {
	const value = String(input || '').trim();
	const identified = EXTERNAL_SOURCES.find(source => source.identifiers?.some(pattern => pattern.test(value)));
	if (identified) return identified;

	try {
		const hostname = new URL(value).hostname.toLowerCase();
		return EXTERNAL_SOURCES.find(source => source.hosts.some(pattern => pattern.test(hostname))) || null;
	} catch {
		return null;
	}
}

class Player {
	constructor(manager, { guild, voiceChannel, textChannel, selfDeafen = true }) {
		this.manager = manager;
		this.guild = guild;
		this.voiceChannel = voiceChannel;
		this.textChannel = textChannel;
		this.selfDeafen = selfDeafen;
		this.queue = new Queue();
		this.previousTracks = [];
		this.timeout = null;
		this.volume = 100;
		this.playing = false;
		this.paused = false;
		this.state = 'DISCONNECTED';
		this.position = 0;
		this.trackRepeat = false;
		this.queueRepeat = false;
		this.autoplay = false;
		this.twentyFourSeven = false;
		this.speed = 1;
		this.bassboost = false;
		this.nightcore = false;
		this.slowmo = false;
		this.vaporwave = false;
		this.filter = {};
		this.presetTimescale = null;
		this.connection = null;
		this.connecting = null;
		this.startedAt = 0;
		this.stopRequested = false;
		this.ignoreNextIdle = false;
		this.destroyed = false;
		this.filters = { clearFilters: () => this.resetFilter() };

		this.audioPlayer = createAudioPlayer();
		this.audioPlayer.on(AudioPlayerStatus.Playing, () => {
			this.playing = true;
			this.paused = false;
			this.startedAt = Date.now();
		});
		this.audioPlayer.on(AudioPlayerStatus.Paused, () => {
			this.paused = true;
		});
		this.audioPlayer.on(AudioPlayerStatus.Idle, () => this._handleIdle());
		this.audioPlayer.on('error', error => this._onError(error));
	}

	get guildObject() {
		return this.manager.bot.guilds.cache.get(this.guild);
	}

	get currentPosition() {
		if (this.paused) return this.position;
		return this.position + (this.startedAt ? Date.now() - this.startedAt : 0);
	}

	async connect() {
		if (this.destroyed) throw new Error('Player has been destroyed.');
		if (this.connection?.state.status === VoiceConnectionStatus.Ready) return this.connection;
		if (this.connecting) return this.connecting;

		const guild = this.guildObject;
		if (!guild?.voiceAdapterCreator) throw new Error('Guild voice adapter is not ready.');

		this.state = 'CONNECTING';
		this.connection = joinVoiceChannel({
			channelId: this.voiceChannel,
			guildId: this.guild,
			adapterCreator: guild.voiceAdapterCreator,
			selfDeaf: this.selfDeafen,
		});
		this.connection.subscribe(this.audioPlayer);
		this.connection.on(VoiceConnectionStatus.Disconnected, async () => {
			try {
				await entersState(this.connection, VoiceConnectionStatus.Connecting, 5000);
			} catch {
				if (!this.destroyed) this.destroy();
			}
		});

		this.connecting = entersState(this.connection, VoiceConnectionStatus.Ready, 30000)
			.then(connection => {
				this.state = 'CONNECTED';
				return connection;
			})
			.finally(() => {
				this.connecting = null;
			});
		return this.connecting;
	}

	async setVoiceChannel(channel) {
		this.voiceChannel = typeof channel === 'string' ? channel : channel.id;
		if (!this.connection) return this.connect();

		this.connection.rejoin({
			channelId: this.voiceChannel,
			selfDeaf: this.selfDeafen,
		});
		await entersState(this.connection, VoiceConnectionStatus.Ready, 15000);
		this.state = 'CONNECTED';
		return this;
	}

	async search(query, requester) {
		try {
			if (typeof query === 'object') {
				if (query.source === 'speak') return this._searchSpeech(query.query, requester);
				if (query.source === 'upload') return this._searchUploadedFile(query.attachment, requester);
			}

			const value = String(query || '').trim();
			if (!value) return { loadType: 'empty', tracks: [] };
			if (/^(?:ftts:\/\/|tts:)/i.test(value)) return this._searchFloweryTTS(value, requester);
			if (/^speak:/i.test(value)) return this._searchSpeech(value.replace(/^speak:/i, ''), requester);
			if (this._isStreamDeckAudio(value)) return this._searchStreamDeck(value, requester);

			const externalSource = getExternalSource(value);
			if (externalSource) return this._searchExternal(value, externalSource, requester);

			const url = isUrl(value);
			const info = await youtubedl(url ? value : `ytsearch1:${value}`, {
				dumpSingleJson: true,
				skipDownload: true,
				noWarnings: true,
				noCallHome: true,
				playlistEnd: 100,
			});
			const entries = (info.entries || []).filter(Boolean);

			if (!url && entries[0]) {
				return { loadType: 'search', tracks: [this._track(entries[0], requester)] };
			}
			if (entries.length) {
				const tracks = entries.map(entry => this._track(entry, requester));
				return {
					loadType: 'playlist',
					playlist: { name: info.title, tracks },
					tracks,
				};
			}
			if (info?.title) return { loadType: 'search', tracks: [this._track(info, requester)] };
			return { loadType: 'empty', tracks: [] };
		} catch (exception) {
			return { loadType: 'error', exception, tracks: [] };
		}
	}

	get musicConfig() {
		return this.manager.bot.config?.Music || {};
	}

	_isProviderEnabled(provider) {
		const configured = this.musicConfig.disabledProviders || [];
		const disabled = new Set((Array.isArray(configured) ? configured : String(configured).split(','))
			.map(value => String(value).trim().toLowerCase()));
		return !disabled.has(String(provider).toLowerCase());
	}

	_assertProviderEnabled(provider) {
		if (!this._isProviderEnabled(provider)) {
			throw new Error(`${providerNames[provider] || provider} is disabled by this bot's configuration.`);
		}
	}

	_searchFloweryTTS(query, requester) {
		this._assertProviderEnabled('flowerytts');
		const rawText = String(query).replace(/^tts:/i, '');
		const encodedText = rawText.replace(/^ftts:\/\//i, '').split('?')[0];
		let text;
		try {
			text = decodeURIComponent(encodedText).trim();
		} catch {
			text = encodedText.trim();
		}
		if (!text) throw new Error('TTS text is required. Use ftts://Hello world.');
		if (text.length > 2048) throw new Error('TTS text must be 2048 characters or fewer.');

		const config = this.musicConfig.floweryTts || {};
		const queryOptions = new URLSearchParams(String(query).split('?').slice(1).join('?'));
		const apiUrl = String(config.apiUrl || 'https://api.flowery.pw/v1/tts').replace(/\/+$/, '');
		const params = new URLSearchParams({
			text,
			translate: queryOptions.get('translate') ?? String(Boolean(config.translate)),
			silence: queryOptions.get('silence') ?? String(number(config.silence)),
			speed: queryOptions.get('speed') ?? String(number(config.speed) || 1),
			audio_format: queryOptions.get('audio_format') ?? (config.audioFormat || 'mp3'),
		});
		const voice = queryOptions.get('voice') ?? config.voice;
		if (voice) params.set('voice', voice);

		return {
			loadType: 'search',
			tracks: [this._directTrack({
				title: text,
				author: 'Flowery TTS',
				uri: `${apiUrl}?${params}`,
				identifier: crypto.createHash('sha256').update(text).digest('hex'),
				provider: 'flowerytts',
			}, requester)],
		};
	}

	_searchSpeech(input, requester) {
		this._assertProviderEnabled('speechtts');
		const text = String(input || '').trim();
		if (!text) return { loadType: 'empty', tracks: [] };
		if (text.length > 200) throw new Error('Speech text must be 200 characters or fewer.');

		const params = new URLSearchParams({
			tl: this.musicConfig.speechTts?.language || 'en-AU',
			q: text,
			ie: 'UTF-8',
			total: '1',
			idx: '0',
			textlen: String(text.length),
			client: 'tw-ob',
		});
		return {
			loadType: 'search',
			tracks: [this._directTrack({
				title: `Speaking ${text}`,
				author: 'Google TTS',
				uri: `https://translate.google.com/translate_tts?${params}`,
				identifier: crypto.createHash('sha256').update(`${params.get('tl')}:${text}`).digest('hex'),
				provider: 'speechtts',
			}, requester)],
		};
	}

	_searchUploadedFile(attachment, requester) {
		this._assertProviderEnabled('upload');
		if (!attachment?.url || !attachment?.name) {
			throw new Error('Please attach an audio or video file.');
		}

		const maxMegabytes = Math.max(1, number(this.musicConfig.uploads?.maxMegabytes) || 25);
		if (number(attachment.size) > maxMegabytes * 1024 * 1024) {
			throw new Error(`Uploads must be ${maxMegabytes} MB or smaller.`);
		}

		const extension = path.extname(attachment.name).toLowerCase();
		const mediaType = attachment.contentType || '';
		const extensions = new Set(['.mp3', '.wav', '.ogg', '.flac', '.m4a', '.aac', '.wma', '.opus', '.webm', '.mp4', '.mkv', '.avi', '.mov']);
		if (!extensions.has(extension) && !/^(audio|video)\//i.test(mediaType)) {
			throw new Error('Unsupported upload type. Attach an audio or video file.');
		}

		return {
			loadType: 'search',
			tracks: [this._directTrack({
				title: path.basename(attachment.name, extension) || attachment.name,
				author: 'Discord upload',
				uri: attachment.url,
				identifier: attachment.id || crypto.createHash('sha256').update(attachment.url).digest('hex'),
				provider: 'upload',
				thumbnail: /^video\//i.test(mediaType) ? attachment.url : null,
				getStream: async () => (await axios.get(attachment.url, {
					responseType: 'stream',
					timeout: 30000,
					headers: { 'User-Agent': 'Mozilla/5.0' },
				})).data,
			}, requester)],
		};
	}

	_isStreamDeckAudio(value) {
		try {
			const url = new URL(value);
			return /^https?:$/.test(url.protocol) && url.pathname.toLowerCase().endsWith('.streamdeckaudio');
		} catch {
			return false;
		}
	}

	_searchStreamDeck(url, requester) {
		this._assertProviderEnabled('streamdeck');
		const filename = new URL(url).pathname.split('/').pop() || 'Stream Deck audio';
		return {
			loadType: 'search',
			tracks: [this._directTrack({
				title: filename.replace(/\.streamdeckaudio$/i, ''),
				author: 'Elgato Stream Deck',
				uri: url,
				identifier: crypto.createHash('sha256').update(url).digest('hex'),
				provider: 'streamdeck',
				getStream: () => this._getStreamDeckStream(url),
			}, requester)],
		};
	}

	async _searchExternal(value, source, requester) {
		this._assertProviderEnabled(source.id);
		if (source.nsfw && !this.guildObject?.channels.cache.get(this.textChannel)?.nsfw) {
			throw new Error(`${source.label} can only be used in an age-restricted channel.`);
		}

		const input = source.id === 'ocremix' && /^OCR\d+$/i.test(value)
			? `https://ocremix.org/remix/${value.toUpperCase()}`
			: (source.id === 'pornhub' && /^phsearch:/i.test(value) ? `phsearch1:${value.slice(9).trim()}` : value);
		const info = await youtubedl(input, {
			dumpSingleJson: true,
			skipDownload: true,
			noCheckCertificates: true,
			noWarnings: true,
			playlistEnd: 100,
		});
		const entries = (info.entries || []).filter(Boolean);
		const tracks = (entries.length ? entries : (info ? [info] : [])).map(entry => this._track(entry, requester, {
			provider: source.id,
			external: true,
			getStream: () => this._getExternalInput(entry.webpage_url || entry.original_url || entry.url || input),
		}));
		return entries.length
			? { loadType: 'playlist', playlist: { name: info.title, tracks }, tracks }
			: { loadType: tracks.length ? 'search' : 'empty', tracks };
	}

	async _getStreamDeckStream(url) {
		const response = await axios.get(url, { responseType: 'stream', timeout: 30000 });
		const decoder = new Transform({
			transform(chunk, encoding, callback) {
				const decoded = Buffer.from(chunk);
				for (let index = 0; index < decoded.length; index++) decoded[index] ^= 0x5E;
				callback(null, decoded);
			},
		});
		return response.data.pipe(decoder);
	}

	async _getExternalInput(url) {
		const options = {
			dumpSingleJson: true,
			format: 'bestaudio[protocol^=http]/bestaudio',
			noCheckCertificates: true,
			noWarnings: true,
		};
		const info = await youtubedl(url, options);
		if (info?.url && /^https?$/.test(info.protocol || '')) {
			return { url: info.url, headers: info.http_headers || {} };
		}

		const process = youtubedl.exec(url, {
			format: 'bestaudio',
			output: '-',
			quiet: true,
			noCheckCertificates: true,
		});
		process.catch(() => null);
		return process.stdout;
	}

	_directTrack(data, requester) {
		return {
			title: data.title,
			author: data.author,
			duration: 0,
			uri: data.uri,
			streamUrl: data.uri,
			identifier: data.identifier || data.uri,
			thumbnail: null,
			requester,
			isSeekable: false,
			provider: data.provider,
			getStream: data.getStream,
		};
	}

	_track(info, requester, extra = {}) {
		const uri = info.webpage_url || info.original_url || info.url;
		return {
			title: info.title || 'Unknown track',
			author: info.uploader || info.channel || info.artist || 'Unknown artist',
			duration: Math.round(number(info.duration) * 1000),
			uri,
			streamUrl: info.url || null,
			identifier: info.id || uri,
			thumbnail: info.thumbnail || null,
			requester,
			isSeekable: !info.is_live && !info.live_status,
			...extra,
		};
	}

	async play() {
		if (this.destroyed) return;
		if (!this.queue.current) this.queue.current = this.queue.shift();
		if (!this.queue.current) return;

		await this.connect();
		this.stopRequested = false;
		return this._start(this.queue.current, this.position);
	}

	async _start(track, offset = 0) {
		this.position = Math.max(0, number(offset));
		const resolvedInput = track.getStream ? await track.getStream() : null;
		const stream = resolvedInput && typeof resolvedInput.pipe === 'function' ? resolvedInput : null;
		const streamUrl = resolvedInput && typeof resolvedInput === 'object' ? resolvedInput.url : resolvedInput;
		const input = stream ? null : (typeof streamUrl === 'string' ? streamUrl : (track.streamUrl || await youtubedl(track.uri, {
			getUrl: true,
			format: 'bestaudio/best',
			noWarnings: true,
			noCallHome: true,
			noPlaylist: true,
		})));
		const filters = this._ffmpegFilters();
		const args = ['-hide_banner', '-loglevel', 'error'];

		if (this.position) args.push('-ss', (this.position / 1000).toFixed(3));
		const headers = resolvedInput?.headers;
		if (!stream && headers && Object.keys(headers).length) {
			args.push('-headers', Object.entries(headers).map(([name, value]) => `${name}: ${value}`).join('\r\n'));
		}
		args.push('-i', stream ? 'pipe:0' : String(input).trim(), '-vn');
		if (filters.length) args.push('-af', filters.join(','));
		args.push('-f', 's16le', '-ar', '48000', '-ac', '2', 'pipe:1');

		const ffmpeg = spawn(ffmpegPath, args, {
			stdio: [stream ? 'pipe' : 'ignore', 'pipe', 'pipe'],
			windowsHide: true,
		});
		if (stream) {
			stream.once('error', error => this._onError(error));
			stream.pipe(ffmpeg.stdin);
		}
		let details = '';
		ffmpeg.stderr.on('data', data => {
			details += data.toString();
		});
		ffmpeg.once('error', error => this._onError(error));
		ffmpeg.once('close', code => {
			if (code && !this.stopRequested && details) {
				this._onError(new Error(details.trim()));
			}
		});

		this.resource = createAudioResource(ffmpeg.stdout, {
			inputType: StreamType.Raw,
			inlineVolume: true,
		});
		this.resource.volume.setVolume(this.volume / 100);
		this.audioPlayer.play(this.resource);
		this.manager.emit('trackStart', this, track);
	}

	_ffmpegFilters() {
		const filters = [];
		const bass = typeof this.bassboost === 'number'
			? this.bassboost
			: (this.bassboost ? 0.65 : 0);
		const timescale = this.presetTimescale || this.filter.timescale || {};
		const speed = number(timescale.speed ?? this.speed ?? 1);
		const pitch = number(timescale.pitch ?? 1);

		if (bass) filters.push(`equalizer=f=100:t=q:w=1:g=${bass * 10}`);
		if (pitch !== 1) filters.push(`asetrate=48000*${pitch}`, 'aresample=48000');
		if (speed !== 1) filters.push(`atempo=${Math.max(0.5, Math.min(2, speed))}`);
		return filters;
	}

	_handleIdle() {
		if (this.ignoreNextIdle) {
			this.ignoreNextIdle = false;
			return;
		}
		this._onIdle();
	}

	_onIdle() {
		if (!this.queue.current || this.destroyed) return;

		const ended = this.queue.current;
		this.queue.previous = ended;
		this.previousTracks.push(ended);
		this.manager.emit('trackEnd', this, ended);

		if (this.trackRepeat && !this.stopRequested) return this._start(ended);
		if (this.queueRepeat && !this.stopRequested) this.queue.push(ended);

		this.queue.current = this.queue.shift() || null;
		this.position = 0;
		this.startedAt = 0;
		if (this.queue.current) {
			this.stopRequested = false;
			return this._start(this.queue.current);
		}

		this.playing = false;
		this.manager.emit('queueEnd', this, ended);
	}

	_onError(error) {
		if (this.destroyed || this.stopRequested) return;
		this.manager.emit('trackError', this, this.queue.current, {
			error: error.message || String(error),
		});
		this.stopRequested = true;
		this.audioPlayer.stop(true);
	}

	pause(value) {
		if (value) {
			this.position = this.currentPosition;
			this.audioPlayer.pause(true);
			this.paused = true;
		} else {
			this.audioPlayer.unpause();
			this.paused = false;
			this.startedAt = Date.now();
		}
		return this;
	}

	stop(amount = 0) {
		if (amount > 1) this.queue.splice(0, amount - 1);
		this.stopRequested = true;
		this.audioPlayer.stop(true);
		return this;
	}

	async seek(position) {
		this.position = Math.max(0, number(position));
		this.ignoreNextIdle = true;
		this.stopRequested = true;
		this.audioPlayer.stop(true);
		this.stopRequested = false;
		try {
			return await this._start(this.queue.current, this.position);
		} catch (error) {
			this.ignoreNextIdle = false;
			throw error;
		}
	}

	setVolume(value) {
		this.volume = Math.max(0, Math.min(1000, number(value)));
		this.resource?.volume?.setVolume(this.volume / 100);
		return this;
	}

	setTrackRepeat(value) {
		this.trackRepeat = Boolean(value);
		if (value) this.queueRepeat = false;
		return this;
	}

	setQueueRepeat(value) {
		this.queueRepeat = Boolean(value);
		if (value) this.trackRepeat = false;
		return this;
	}

	setSpeed(value) {
		this.speed = Math.max(0.5, Math.min(2, number(value) || 1));
		return this._restartForFilter();
	}

	setBassboost(value) {
		this.bassboost = value === true ? 0.65 : (value === false ? false : number(value) || false);
		return this._restartForFilter();
	}

	setNightcore(value) {
		return this._setPreset('nightcore', value, { speed: 1.2, pitch: 1.2 });
	}

	setVaporwave(value) {
		return this._setPreset('vaporwave', value, { speed: 0.7, pitch: 0.8 });
	}

	setSlowmo(value) {
		return this._setPreset('slowmo', value, { speed: 0.7, pitch: 1 });
	}

	_setPreset(name, value, timescale) {
		this[name] = Boolean(value);
		if (value) {
			for (const preset of ['nightcore', 'vaporwave', 'slowmo']) {
				if (preset !== name) this[preset] = false;
			}
			this.presetTimescale = timescale;
		} else {
			this.presetTimescale = null;
		}
		return this._restartForFilter();
	}

	setFilter(filter = {}) {
		this.filter = { ...this.filter, ...filter };
		return this._restartForFilter();
	}

	resetFilter(restart = true) {
		this.filter = {};
		this.presetTimescale = null;
		this.speed = 1;
		this.bassboost = false;
		this.nightcore = false;
		this.slowmo = false;
		this.vaporwave = false;
		return restart ? this._restartForFilter() : this;
	}

	_restartForFilter() {
		if (this.playing && this.queue.current) {
			this.seek(this.currentPosition).catch(error => this._onError(error));
		}
		return this;
	}

	addPreviousSong(song) {
		if (!this.previousTracks.includes(song)) this.previousTracks.push(song);
		return this;
	}

	destroy() {
		if (this.destroyed) return;

		this.destroyed = true;
		clearTimeout(this.timeout);
		this.audioPlayer.stop(true);
		this.connection?.destroy();
		this.state = 'DISCONNECTED';
		this.manager.players.delete(this.guild);
		this.manager.emit('playerDestroy', this);
	}
}

class AudioManager extends EventEmitter {
	constructor(bot) {
		super();
		this.bot = bot;
		this.players = new Map();
	}

	init() {
		return this;
	}

	updateVoiceState() {
		return this;
	}

	create(options) {
		const existing = this.players.get(options.guild);
		if (existing) return existing;

		const player = new Player(this, options);
		this.players.set(options.guild, player);
		this.emit('playerCreate', player);
		return player;
	}

	async search(query, requester) {
		const player = new Player(this, {
			guild: '',
			voiceChannel: '',
			textChannel: '',
		});
		const result = await player.search(query, requester);
		player.audioPlayer.stop(true);
		return result;
	}
}

AudioManager.buildUnresolved = (data, requester) => ({
	title: data.title || 'Unknown track',
	author: data.author || 'Unknown artist',
	duration: number(data.duration),
	uri: `ytsearch1:${data.title || ''} ${data.author || ''}`,
	identifier: data.identifier || data.title,
			thumbnail: data.thumbnail || null,
	requester,
	isSeekable: true,
});

module.exports = AudioManager;
