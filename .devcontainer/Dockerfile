FROM mcr.microsoft.com/devcontainers/python:1-3.12-bookworm

USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl ca-certificates git make zstd libgmp-dev \
    && rm -rf /var/lib/apt/lists/*
USER vscode
ENV PATH="/home/vscode/.local/bin:/home/vscode/.elan/bin:${PATH}"
RUN curl -LsSf https://astral.sh/uv/0.11.20/install.sh | sh \
    && curl -sSf https://raw.githubusercontent.com/leanprover/elan/v4.2.3/elan-init.sh | sh -s -- -y --default-toolchain none
