#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# The editor is connected now, so it sees the studio's port open and forwards it.
bash .devcontainer/studio.sh
code --install-extension extensions/vscode/dist/statclaim.vsix --force
printf '\nOpen playground/welcome.stat. If needed, run Developer: Reload Window.\n'
