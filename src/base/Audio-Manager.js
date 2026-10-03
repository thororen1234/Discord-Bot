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
const { Deezer, AppleMusic } = require('./music/Catalogs');
const SongLink = require('./music/SongLink');
const Spotify = require('./music/Spotify');
const Tidal = require('./music/Tidal');
const { normalizeTitle, isExactTrackMatch } = require('./music/TrackMatch');

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
const RESOLVED_TTL = 30 * 60 * 1000;
const MEDIA_EXTENSIONS = new Set(['.mp3', '.wav', '.ogg', '.flac', '.m4a', '.aac', '.wma', '.opus', '.webm', '.mp4', '.mkv', '.avi', '.mov']);

function hostMatches(value, pattern) {
	try {
		return /^https?:$/.test(new URL(value).protocol) && pattern.test(new URL(value).hostname.toLowerCase());
	} catch {
		return false;
	}
}

const isYouTubeUrl = value => hostMatches(value, /(^|\.)(youtube\.com|youtu\.be|youtube-nocookie\.com)$/);
const isSoundCloudUrl = value => hostMatches(value, /(^|\.)soundcloud\.com$|^on\.soundcloud\.com$/);

function isDirectMediaUrl(value) {
	try {
		const url = new URL(value);
		return /^https?:$/.test(url.protocol) && MEDIA_EXTENSIONS.has(path.extname(url.pathname).toLowerCase());
	} catch {
		return false;
	}
}

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
	applemusic: 'Apple Music',
	deezer: 'Deezer',
	direct: 'Direct links',
	soundcloud: 'SoundCloud',
	spotify: 'Spotify',
	tidal: 'Tidal',
	youtube: 'YouTube',
	http: 'Other links',
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

	/**
	 * Resolves a query, link or attachment into tracks.
	 * @param {string|object} query The search text, link, or { source, ... } object for TTS/uploads
	 * @param {User} requester Who asked for the track(s)
	 * @param {string} [source] Where plain-text searches play from: youtube, soundcloud or tidal
	*/
	async search(query, requester, source) {
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
			if (isYouTubeUrl(value)) return await this._searchYouTube(value, requester);

			const linkProvider = SongLink.getProviderId(value);
			if (linkProvider) return await this._searchMusicService(value, linkProvider, requester, source);
			if (isSoundCloudUrl(value)) return await this._searchSoundCloud(value, requester);

			const externalSource = getExternalSource(value);
			if (externalSource) return await this._searchExternal(value, externalSource, requester);
			if (isDirectMediaUrl(value)) return this._searchDirect(value, requester);
			if (isUrl(value)) return await this._searchLink(value, requester);

			return await this._searchText(value, requester, source);
		} catch (exception) {
			return { loadType: 'error', exception, tracks: [] };
		}
	}

	get musicConfig() {
		return this.manager.bot.config?.Music || {};
	}

	get maxPlaylistSize() {
		return Math.max(1, number(this.musicConfig.maxPlaylistSize) || 100);
	}

	// Common yt-dlp options, including YouTube authentication (PO token > browser cookies > cookie file)
	_ytdlOptions(extra = {}) {
		const config = this.musicConfig.youtube || {};
		const options = {
			// Only use this config, not a yt-dlp config file that happens to be on the host
			ignoreConfig: true,
			noCheckCertificates: true,
			noWarnings: true,
			// yt-dlp needs a JavaScript runtime to solve YouTube's player challenges
			jsRuntimes: `node:${process.execPath}`,
			...extra,
		};

		if (config.poToken) {
			// Tokens are given as CLIENT.CONTEXT+TOKEN, a bare token is a web streaming (GVS) token
			const token = config.poToken.includes('+') ? config.poToken : `web.gvs+${config.poToken}`;
			options.extractorArgs = `youtube:po_token=${token}`;
		} else if (config.cookiesFromBrowser) {
			options.cookiesFromBrowser = config.cookiesFromBrowser;
		} else if (config.cookiesFile) {
			options.cookies = config.cookiesFile;
		}
		return options;
	}

	_result({ name, tracks }, requester) {
		for (const track of tracks) track.requester = requester;
		if (!tracks.length) return { loadType: 'empty', tracks };
		return name
			? { loadType: 'playlist', playlist: { name, tracks }, tracks }
			: { loadType: 'search', tracks };
	}

	_thumbnail(info) {
		return info.thumbnail || info.thumbnails?.[info.thumbnails.length - 1]?.url || null;
	}

	// YouTube videos and playlists. Playlists are read flat, so each entry's stream is only resolved when it plays.
	async _searchYouTube(url, requester) {
		this._assertProviderEnabled('youtube');
		const info = await youtubedl(url, this._ytdlOptions({
			dumpSingleJson: true,
			skipDownload: true,
			flatPlaylist: true,
			playlistEnd: this.maxPlaylistSize,
		}));
		const entries = (info?.entries || []).filter(entry => entry && (entry.id || entry.url));
		if (entries.length) {
			const tracks = entries.map(entry => this._track(entry, requester, { provider: 'youtube' }));
			return { loadType: 'playlist', playlist: { name: info.title, tracks }, tracks };
		}
		return info?.title
			? { loadType: 'search', tracks: [this._track(info, requester, { provider: 'youtube' })] }
			: { loadType: 'empty', tracks: [] };
	}

	// Any other link yt-dlp has an extractor for (Bandcamp, Vimeo, Twitch, ...)
	async _searchLink(url, requester) {
		this._assertProviderEnabled('http');
		const info = await youtubedl(url, this._ytdlOptions({
			dumpSingleJson: true,
			skipDownload: true,
			playlistEnd: this.maxPlaylistSize,
		}));
		const entries = (info?.entries || []).filter(Boolean);
		const tracks = (entries.length ? entries : (info?.title ? [info] : [])).map(entry => this._track(entry, requester, {
			provider: 'http',
		}));
		return entries.length
			? { loadType: 'playlist', playlist: { name: info.title, tracks }, tracks }
			: { loadType: tracks.length ? 'search' : 'empty', tracks };
	}

	// Plain-text search. Tidal and SoundCloud only answer with a good match, otherwise YouTube is used.
	async _searchText(query, requester, source) {
		const from = String(source || this.musicConfig.defaultSource || 'youtube').toLowerCase();

		if (from === 'tidal' && this.manager.tidal.configured && this._isProviderEnabled('tidal')) {
			try {
				const match = await this.manager.tidal.findExact(query);
				if (match) return this._result({ tracks: [match] }, requester);
			} catch (err) {
				this._debug(err.message);
			}
		}

		if (from === 'soundcloud' && this._isProviderEnabled('soundcloud')) {
			try {
				const results = await youtubedl(`scsearch5:${query}`, this._ytdlOptions({ dumpSingleJson: true, flatPlaylist: true }));
				const track = (results?.entries || [])
					.map(entry => this._soundCloudTrack(entry, requester))
					.find(result => !result.preview);
				if (track) return { loadType: 'search', tracks: [track] };
			} catch (err) {
				this._debug(err.message);
			}
		}

		this._assertProviderEnabled('youtube');
		const results = await youtubedl(`ytsearch1:${query}`, this._ytdlOptions({ dumpSingleJson: true, flatPlaylist: true }));
		const entry = (results?.entries || []).find(Boolean);
		return entry
			? { loadType: 'search', tracks: [this._track(entry, requester, { provider: 'youtube' })] }
			: { loadType: 'empty', tracks: [] };
	}

	async _searchSoundCloud(url, requester) {
		this._assertProviderEnabled('soundcloud');
		const info = await youtubedl(url, this._ytdlOptions({
			dumpSingleJson: true,
			skipDownload: true,
			playlistEnd: this.maxPlaylistSize,
		}));
		const entries = (info?.entries || []).filter(Boolean);
		const tracks = (entries.length ? entries : (info ? [info] : [])).map(entry => this._soundCloudTrack(entry, requester));
		return entries.length
			? { loadType: 'playlist', playlist: { name: info.title, tracks }, tracks }
			: { loadType: tracks.length ? 'search' : 'empty', tracks };
	}

	// SoundCloud only serves 30 second previews of some label tracks, so those play the full song from YouTube
	_soundCloudTrack(info, requester) {
		const formats = info.formats || [];
		const preview = formats.length
			? formats.every(format => /preview/.test(format.format_id || ''))
			: number(info.duration) > 0 && number(info.duration) <= 30;
		const uri = info.webpage_url || info.url;
		const track = this._track(info, requester, {
			provider: 'soundcloud',
			preview,
			getStream: preview ? undefined : () => this._getExternalInput(uri),
		});
		if (preview) {
			track.duration = 0;
			track.query = `${track.title} ${track.author}`;
		}
		return track;
	}

	_searchDirect(url, requester) {
		this._assertProviderEnabled('direct');
		const { hostname, pathname } = new URL(url);
		let filename = path.basename(pathname);
		try {
			filename = decodeURIComponent(filename);
		} catch {
			// Keep the raw name when it isn't valid percent-encoding
		}
		return {
			loadType: 'search',
			tracks: [this._directTrack({
				title: path.parse(filename).name || filename,
				author: hostname,
				uri: url,
				identifier: crypto.createHash('sha256').update(url).digest('hex'),
				provider: 'direct',
			}, requester)],
		};
	}

	async _searchMusicService(url, provider, requester, source) {
		this._assertProviderEnabled(provider);
		const { tidal, spotify, songlink } = this.manager;
		const limit = this.maxPlaylistSize;

		if (provider === 'tidal' && tidal.configured && Tidal.parseURL(url)) {
			try {
				const result = await tidal.getFromURL(url, limit);
				if (result.tracks.length) return this._result(result, requester);
			} catch (err) {
				this._debug(err.message);
			}
		}

		// SongLink only matches single songs, so Spotify albums, playlists and artists need the Spotify API
		const spotifyRef = provider === 'spotify' ? Spotify.parseURL(url) : null;
		if (spotifyRef && spotifyRef.type !== 'track') {
			if (!spotify.configured) throw new Error('Spotify albums, playlists and artists need Spotify API credentials in the bot\'s config.');
			return this._result(await spotify.getFromURL(url, limit), requester);
		}

		let lookupError;
		if (songlink.configured) {
			try {
				const song = await songlink.lookup(url);
				const result = await this._fromSongLink(song, url, source, requester);
				if (result) return result;
			} catch (err) {
				lookupError = err;
			}
		}

		// Without SongLink, read the metadata from the service itself and find the songs on YouTube
		if (spotifyRef && spotify.configured) return this._result(await spotify.getFromURL(url, limit), requester);
		if (provider === 'deezer') return this._result(await Deezer.getFromURL(url, limit), requester);
		if (provider === 'applemusic') return this._result(await AppleMusic.getFromURL(url, limit), requester);
		const needs = provider === 'tidal' ? 'a Tidal (TidalSubsonic) server' : 'Spotify API credentials';
		throw lookupError || new Error(`${providerNames[provider]} links need ${needs} or a SongLink API in the bot's config.`);
	}

	async _fromSongLink(song, url, source, requester) {
		const { tidal } = this.manager;
		if (source === 'tidal' || SongLink.getProviderId(url) === 'tidal') {
			if (tidal.configured && this._isProviderEnabled('tidal') && Tidal.parseURL(song.tidalUrl)) {
				try {
					const result = await tidal.getFromURL(song.tidalUrl, this.maxPlaylistSize);
					// Only trust the Tidal match when it is exactly the requested song/album
					const exact = !song.title || (song.type === 'album'
						? normalizeTitle(song.title) === normalizeTitle(result.tracks[0]?.album)
						: result.tracks[0] && isExactTrackMatch(song, result.tracks[0]));
					if (result.tracks.length && exact) return this._result(result, requester);
				} catch (err) {
					this._debug(err.message);
				}
			}
		}

		this._assertProviderEnabled('youtube');
		if (song.youtubeUrl) {
			const result = await this._searchYouTube(song.youtubeUrl, requester);
			// Play the YouTube audio, but keep the clean metadata from the source service
			if (result.loadType === 'search') {
				Object.assign(result.tracks[0], {
					title: song.title || result.tracks[0].title,
					author: song.author || result.tracks[0].author,
					thumbnail: song.thumbnail || result.tracks[0].thumbnail,
					sourceUri: url,
				});
			}
			if (result.tracks.length) return result;
		}

		if (song.type === 'album') throw new Error('SongLink couldn\'t find this album on YouTube.');
		if (!song.title) return null;

		// No direct YouTube link - find the song on YouTube when it starts playing
		return this._result({
			tracks: [{
				title: song.title,
				author: song.author || 'Unknown artist',
				duration: 0,
				uri: url,
				identifier: url,
				thumbnail: song.thumbnail,
				isSeekable: true,
				provider: SongLink.getProviderId(url),
				query: [song.title, song.author].filter(Boolean).join(' '),
			}],
		}, requester);
	}

	_debug(message) {
		if (this.manager.bot.config?.debug) this.manager.bot.logger.debug(`Music: ${message}`);
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
		if (!MEDIA_EXTENSIONS.has(extension) && !/^(audio|video)\//i.test(mediaType)) {
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
		const info = await youtubedl(input, this._ytdlOptions({
			dumpSingleJson: true,
			skipDownload: true,
			playlistEnd: this.maxPlaylistSize,
		}));
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
		const info = await youtubedl(url, this._ytdlOptions({
			dumpSingleJson: true,
			format: 'bestaudio[protocol^=http]/bestaudio',
		}));
		if (info?.url && /^https?$/.test(info.protocol || '')) {
			return { url: info.url, headers: info.http_headers || {} };
		}

		// HLS/DASH-only sources are piped through yt-dlp instead
		const subprocess = youtubedl.exec(url, this._ytdlOptions({
			format: 'bestaudio',
			output: '-',
			quiet: true,
		}));
		subprocess.catch(() => null);
		return subprocess.stdout;
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
		const live = info.is_live || ['is_live', 'is_upcoming', 'post_live'].includes(info.live_status);
		return {
			title: info.title || 'Unknown track',
			author: info.uploader || info.channel || info.artist || 'Unknown artist',
			duration: Math.round(number(info.duration) * 1000),
			uri,
			// Stream URLs are resolved when the track starts, since they expire
			streamUrl: null,
			identifier: info.id || uri,
			thumbnail: this._thumbnail(info),
			requester,
			isSeekable: !live,
			...extra,
		};
	}

	async play() {
		if (this.destroyed) return;
		if (!this.queue.current) this.queue.current = this.queue.shift();
		if (!this.queue.current) return;

		try {
			await this.connect();
		} catch (error) {
			this.manager.emit('trackError', this, this.queue.current, { error: `Couldn't join the voice channel: ${error.message}` });
			return this.destroy();
		}
		this.stopRequested = false;
		return this._startOrSkip(this.queue.current, this.position);
	}

	// Starts a track, reporting the error and moving on to the next track if it can't be played
	async _startOrSkip(track, offset = 0) {
		try {
			await this._start(track, offset);
		} catch (error) {
			if (this.destroyed || track !== this.queue.current) return;
			this.manager.emit('trackError', this, track, { error: error.message || String(error) });
			// Never repeat a track that just failed
			this.stopRequested = true;
			this._onIdle();
		}
	}

	// Works out what FFmpeg should read for a track: a readable stream, or a URL with optional headers
	async _resolveInput(track) {
		if (track.getStream) return track.getStream();
		if (track.streamUrl) return { url: track.streamUrl };
		if (track.resolved && Date.now() - track.resolved.at < RESOLVED_TTL) return track.resolved;

		const target = track.query ? await this._findOnYouTube(track) : track.uri;
		const info = await youtubedl(target, this._ytdlOptions({
			dumpSingleJson: true,
			format: 'bestaudio/best',
			noPlaylist: true,
		}));
		const media = info?.entries ? info.entries.find(Boolean) : info;
		if (!media?.url) throw new Error(`No playable stream was found for ${track.title}.`);

		if (!track.duration && media.duration) track.duration = Math.round(number(media.duration) * 1000);
		track.resolved = { url: media.url, headers: media.http_headers || {}, at: Date.now() };
		return track.resolved;
	}

	// Picks the YouTube upload that best matches a track from another service (Spotify, SoundCloud previews, saved playlists)
	async _findOnYouTube(track) {
		this._assertProviderEnabled('youtube');
		if (track.youtubeUri) return track.youtubeUri;

		const results = await youtubedl(`ytsearch5:${track.query}`, this._ytdlOptions({ dumpSingleJson: true, flatPlaylist: true }));
		const candidates = (results?.entries || []).filter(Boolean).map(entry => ({
			title: entry.title,
			author: entry.uploader || entry.channel,
			duration: Math.round(number(entry.duration) * 1000),
			uri: entry.webpage_url || entry.url,
		}));
		if (!candidates.length) throw new Error(`Couldn't find ${track.title} on YouTube.`);

		const title = normalizeTitle(track.title);
		const closeDuration = candidate => !track.duration || !candidate.duration || Math.abs(candidate.duration - track.duration) < 15000;
		const match = candidates.find(candidate => isExactTrackMatch(track, candidate) && closeDuration(candidate))
			|| candidates.find(candidate => normalizeTitle(candidate.title).includes(title) && closeDuration(candidate))
			|| candidates[0];

		track.youtubeUri = match.uri;
		return match.uri;
	}

	async _start(track, offset = 0) {
		this.position = Math.max(0, number(offset));
		const resolvedInput = await this._resolveInput(track);
		if (this.destroyed || track !== this.queue.current) return;

		const stream = resolvedInput && typeof resolvedInput.pipe === 'function' ? resolvedInput : null;
		const input = stream ? null : String(typeof resolvedInput === 'string' ? resolvedInput : resolvedInput?.url || '').trim();
		if (!stream && !input) throw new Error(`No playable stream was found for ${track.title}.`);

		const filters = this._ffmpegFilters();
		const args = ['-hide_banner', '-loglevel', 'error'];

		// Long HTTP streams (e.g. YouTube) can drop mid-track, so let FFmpeg reconnect
		if (/^https?:/i.test(input || '')) args.push('-reconnect', '1', '-reconnect_streamed', '1', '-reconnect_delay_max', '5');
		if (this.position) args.push('-ss', (this.position / 1000).toFixed(3));
		const headers = resolvedInput?.headers;
		if (!stream && headers && Object.keys(headers).length) {
			args.push('-headers', Object.entries(headers).map(([name, value]) => `${name}: ${value}`).join('\r\n'));
		}
		args.push('-i', stream ? 'pipe:0' : input, '-vn');
		if (filters.length) args.push('-af', filters.join(','));
		args.push('-f', 's16le', '-ar', '48000', '-ac', '2', 'pipe:1');

		this._killProcess();
		const ffmpeg = spawn(ffmpegPath, args, {
			stdio: [stream ? 'pipe' : 'ignore', 'pipe', 'pipe'],
			windowsHide: true,
		});
		this.process = ffmpeg;
		if (stream) {
			stream.once('error', error => {
				if (ffmpeg === this.process) this._onError(error);
			});
			// FFmpeg closing early (skip, seek) breaks the pipe - that's expected
			ffmpeg.stdin.on('error', () => null);
			stream.pipe(ffmpeg.stdin);
		}
		let details = '';
		ffmpeg.stderr.on('data', data => {
			details = (details + data.toString()).slice(-4096);
		});
		ffmpeg.once('error', error => {
			if (ffmpeg === this.process) this._onError(error);
		});
		ffmpeg.once('close', code => {
			// Ignore processes that were replaced by a skip, seek or filter change
			if (ffmpeg !== this.process) return;
			this.process = null;
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

	_killProcess() {
		const ffmpeg = this.process;
		this.process = null;
		if (ffmpeg && ffmpeg.exitCode === null) ffmpeg.kill();
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

		this.position = 0;
		this.startedAt = 0;
		if (this.trackRepeat && !this.stopRequested) return this._startOrSkip(ended);
		if (this.queueRepeat && !this.stopRequested) this.queue.push(ended);

		this.queue.current = this.queue.shift() || null;
		if (this.queue.current) {
			this.stopRequested = false;
			return this._startOrSkip(this.queue.current);
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
		this._killProcess();
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

	get musicConfig() {
		return this.bot.config?.Music || {};
	}

	// Clients for the metadata services, built on first use so config edits apply after a reload
	get songlink() {
		return this._songlink ??= new SongLink(this.musicConfig.songlink);
	}

	get spotify() {
		return this._spotify ??= new Spotify(this.musicConfig.spotify);
	}

	get tidal() {
		return this._tidal ??= new Tidal(this.musicConfig.tidal);
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

	async search(query, requester, source) {
		const player = new Player(this, {
			guild: '',
			voiceChannel: '',
			textChannel: '',
		});
		const result = await player.search(query, requester, source);
		player.audioPlayer.stop(true);
		return result;
	}
}

// Rebuilds a saved track (e.g. from a playlist). YouTube links play directly, anything else is found on YouTube again.
AudioManager.buildUnresolved = (data, requester) => {
	const title = data.title || 'Unknown track';
	const author = data.author || 'Unknown artist';
	const query = `${title} ${author}`;
	const playable = isYouTubeUrl(data.uri);
	return {
		title,
		author,
		duration: number(data.duration),
		uri: isUrl(data.uri) ? data.uri : `https://www.youtube.com/results?search_query=${encodeURIComponent(query)}`,
		streamUrl: null,
		identifier: data.identifier || title,
		thumbnail: data.thumbnail || null,
		requester,
		isSeekable: data.isSeekable ?? true,
		provider: data.provider || 'youtube',
		query: playable ? undefined : query,
	};
};

module.exports = AudioManager;
