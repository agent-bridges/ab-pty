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
#   ./ab-pty genjwt -gen-secret  - generate secret to .jwt-secret
#   ./ab-pty genjwt              - generate token from secret
