FROM gitpod/workspace-full

RUN sudo apt-get update \
 && sudo apt-get install -y \
    curl \
 && sudo rm -rf /var/lib/apt/lists/*

RUN curl -sSL https://get.haskellstack.org/ | sh

ENV PATH=$HOME/.local/bin:$PATH
