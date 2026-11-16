# StatClaim for VS Code

A preview extension for `.stat` diagnostics, completion, public fields and claims.
Install the release VSIX, or use the repository's Codespaces environment.
Open the StatClaim repository as the workspace; Python and Lean run there.

**StatClaim: Show Claims** opens current requirements and matching evidence.
**StatClaim: Explain Contract** shows why the declaration at the cursor passed its
checks. **StatClaim: Show Change Impact** lists what your unsaved edits affect.
**StatClaim: Verify Current File** explicitly runs the backend. Editing checks
compatibility without performing calculations or Lean verification. After edits,
old evidence appears only as historical.

For development, run `npm --prefix extensions/vscode ci --ignore-scripts` from
the repository root and press F5 with **StatClaim Extension** selected.
See the [editor guide](https://github.com/ssm123ssm/statClaim/blob/main/docs/editor.md).
The extension is distributed as a VSIX and is not on the Marketplace.
