#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
code --install-extension extensions/vscode/dist/statproof.vsix --force
printf '\nOpen playground/welcome.stat. If needed, run Developer: Reload Window.\n'
