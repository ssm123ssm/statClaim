# Quickstart

## In the browser

[Create a Codespace](https://codespaces.new/ssm123ssm/statProof). Setup downloads
the pinned Lean toolchain and Mathlib cache, so the first start takes several
minutes. A workspace extension is installed on attachment. Reload the window
if `.stat` support has not appeared. Codespaces uses your GitHub quota.

Open `playground/welcome.stat`. The file is your scratch copy; it is ignored by
git. Edit the null to `proportion_difference(model=study, value=1/10)` and inspect
the diagnostic. Restore equality, then run **StatProof: Verify Current File**.

## Local VS Code

Run `make setup`, then `make editor-package`. Install
`extensions/vscode/dist/statproof.vsix` with **Extensions: Install from VSIX**.
Open this repository as the workspace and trust it. For extension development,
install npm dependencies and press F5; see [editor guide](editor.md).

## Inspect values

The Explorer **StatProof Claims** view displays requirements and matching
evidence. **StatProof: Verify Current File** writes its structured report to
the StatProof output channel. From a terminal:

```sh
uv run --locked statproof check playground/welcome.stat --json
```

The report includes bindings such as `status` and `evidence`. Evidence is optional
and appears only after successful verification. Editing marks earlier results
as historical. `compile` checks the plan without running Lean or writing results.

```sh
uv run --locked statproof compile examples/fisher.stat
uv run --locked statproof catalogue --json
```

If setup fails, run `uv run --locked statproof doctor` and include the output
in an issue. See [development](development.md) for tests and container setup.
