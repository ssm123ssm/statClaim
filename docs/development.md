# Development

Use the README Codespaces button, or install uv, elan and Node.js 22+ locally.
`make setup` installs locked Python dependencies and the pinned Lean/Mathlib
versions. Mathlib needs several GB; its cache download dominates first setup.

```sh
make python-check             # lint, types, tutorial page and fast Python tests
make type-check               # mypy alone
make check                    # plus Lean, axioms and real backend/replay tests
make editor-check             # JS unit tests and real VS Code integration
make catalogue-check repository-check
make tutorial-check           # rerun the lessons and check the outputs the page shows
make editor-package           # distributable VSIX in extensions/vscode/dist
```

CI runs the fast checks, the wheel on two systems and two Python versions, the R
replication, the container, and the Lean integration tests in three parallel shards
(`make integration-shard SHARD=a|b|c`; the last takes every file the first two do
not name). A new push to a pull request cancels its running check; on `main` every
commit is checked to the end.

Type checking is gradual. mypy checks every module except those listed in
`pyproject.toml`; when a module on that list passes, remove it from the list. New
modules are checked from the start.

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
