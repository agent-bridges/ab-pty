FROM golang:1.23-alpine AS builder

RUN apk add --no-cache gcc musl-dev

WORKDIR /build
COPY go.mod go.sum ./
RUN go mod download

COPY *.go ./
ARG VERSION=dev
RUN CGO_ENABLED=1 go build -trimpath -ldflags "-s -w -X main.Version=${VERSION}" -o ab-pty .

FROM alpine:latest

RUN apk add --no-cache bash libc6-compat openssh-client ca-certificates curl nodejs npm jq
RUN npm i -g @openai/codex
RUN curl -fsSL https://claude.ai/install.sh | bash
RUN ln -sf /root/.local/bin/claude /usr/local/bin/claude

WORKDIR /app
COPY --from=builder /build/ab-pty .
COPY claude-hooks-settings.json /app/claude-hooks.json
COPY claude-hook-forwarder.sh /usr/local/bin/claude-hook-forwarder
RUN chmod +x /usr/local/bin/claude-hook-forwarder

ENV AB_PTY_PORT=8421
ENV PATH=/root/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

EXPOSE 8421

CMD ["./ab-pty"]
