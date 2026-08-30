BINARY = ab-pty

.PHONY: build clean version

build:
	@NEW_VER=$$(awk -F. '{print $$1"."$$2"."$$3+1}' VERSION) && echo $$NEW_VER > VERSION && \
	go build -ldflags "-X main.Version=$$NEW_VER" -o $(BINARY) .

clean:
	rm -f $(BINARY)

version:
	@cat VERSION

# Subcommands:
#   ./ab-pty                     - run daemon
#   ./ab-pty version             - show version
#   ./ab-pty client add phone <sha256> operator  - authorize normal daemon use
