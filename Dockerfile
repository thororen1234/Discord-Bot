FROM node:lts-slim

WORKDIR /usr/src/bot

ENV PNPM_HOME="/pnpm"
ENV PATH="$PNPM_HOME:$PATH"

RUN corepack enable

COPY package.json pnpm-lock.yaml ./

RUN pnpm install --prod --frozen-lockfile

COPY . .

CMD ["pnpm", "start"]