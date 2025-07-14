FROM alpine:latest

ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=1000

# Install required packages (Alpine equivalents)
RUN apk add --no-cache \
    curl \
    ca-certificates \
    git \
    build-base \
    gmp-dev \
    zlib-dev \
    sudo \
    bash \
    libc6-compat \
    ncurses-dev \
    xz

# Create user with sudo access
RUN addgroup -g $USER_GID $USERNAME && \
    adduser -D -s /bin/bash -u $USER_UID -G $USERNAME $USERNAME && \
    mkdir -p /etc/sudoers.d && \
    echo "$USERNAME ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/$USERNAME && \
    chmod 0440 /etc/sudoers.d/$USERNAME

USER $USERNAME
WORKDIR /home/$USERNAME

RUN mkdir -p /home/$USERNAME/.ghcup/bin

# Install GHCup
RUN curl -sSL https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup -o /home/$USERNAME/.ghcup/bin/ghcup && \
    chmod +x /home/$USERNAME/.ghcup/bin/ghcup

ENV PATH="/home/$USERNAME/.ghcup/bin:/home/$USERNAME/.cabal/bin:${PATH}"

# Install Haskell toolchain
RUN ghcup install ghc 9.12.2 && \
    ghcup set ghc 9.12.2 && \
    ghcup install hls 2.10.0.0 && \
    ghcup set hls 2.10.0.0 && \
    ghcup install cabal 3.14.2.0 && \
    ghcup set cabal 3.14.2.0 && \
    ln -sf /home/$USERNAME/.ghcup/bin/haskell-language-server-wrapper /home/$USERNAME/.ghcup/bin/hls

# Set up the PATH in bashrc
RUN echo 'export PATH="/home/'$USERNAME'/.ghcup/bin:/home/'$USERNAME'/.cabal/bin:$PATH"' >> /home/$USERNAME/.bashrc

# Verify installations
RUN ghc --version && cabal --version && hls --version

# Update cabal package list
RUN cabal update

ENTRYPOINT ["/bin/bash"]