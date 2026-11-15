# StatProof for VS Code

A preview extension for `.stat` diagnostics, completion, public fields and claims.
Install the release VSIX, or use the repository's Codespaces environment.
Open the StatProof repository as the workspace; Python and Lean run there.

**StatProof: Show Claims** opens current requirements and matching evidence.
**StatProof: Explain Contract** shows why the declaration at the cursor passed its
checks. **StatProof: Show Change Impact** lists what your unsaved edits affect.
**StatProof: Verify Current File** explicitly runs the backend. Editing checks
compatibility without performing calculations or Lean verification. After edits,
old evidence appears only as historical.

For development, run `npm --prefix extensions/vscode ci --ignore-scripts` from
the repository root and press F5 with **StatProof Extension** selected.
See the [editor guide](https://github.com/ssm123ssm/statProof/blob/main/docs/editor.md).
The extension is distributed as a VSIX and is not on the Marketplace.
