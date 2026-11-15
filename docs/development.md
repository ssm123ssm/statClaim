# Development

Use the README Codespaces button, or install uv, elan and Node.js 22+ locally.
`make setup` installs locked Python dependencies and the pinned Lean/Mathlib
versions. Mathlib needs several GB; its cache download dominates first setup.

```sh
make python-check             # lint and fast Python tests
make check                    # plus Lean, axioms and real backend/replay tests
make editor-check             # JS unit tests and real VS Code integration
make catalogue-check repository-check
make editor-package           # distributable VSIX in extensions/vscode/dist
```

On headless Linux use `xvfb-run -a make editor-check`. The test runner downloads
VS Code unless `VSCODE_EXECUTABLE_PATH` selects an installation. Keep Python and
Lean source unchanged while certificate/replay tests run: snapshots hash them.

The devcontainer uses Python 3.12, Node 22, uv and elan. `onCreateCommand` runs
setup and builds the extension; `postAttachCommand` installs it into remote VS
Code. The extension runs in the workspace, so Python/Lean also work in the
browser. Plain vscode.dev without a workspace backend cannot run them.

To test the container locally, install Docker and the Dev Container CLI, then
run `devcontainer up --workspace-folder . --skip-post-attach` for a headless
startup, or use VS Code’s **Reopen in Container**. CI builds the same Dockerfile and
runs bootstrap plus a real sample verification. Optional Codespaces prebuilds
can speed startup; configure them in repository Settings → Codespaces after
reviewing GitHub Actions/storage usage. They are not required to use the button.

Do not commit `.lake`, `.venv`, certificates, VSIX files, agent instructions or
memory notes. An ignored local `AGENTS.md` holds workspace-only preferences.

The packaging tool pins a patched minimatch via npm overrides; remove the override
when vsce adopts it. Run `npm audit` when changing extension dependencies.
