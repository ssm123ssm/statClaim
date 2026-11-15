# StatProof VS Code prototype

From the repository root, run `npm --prefix extensions/vscode ci --ignore-scripts`,
then open the repository in VS Code and press F5 with **StatProof Extension**
selected. The development host recognizes `.stat` files and starts
`uv run --locked statproof lsp` from the StatProof project environment.

Use **StatProof: Verify Current File** for explicit Lean checking and
**StatProof: Restart Language Server** during Python development. Editing itself
only compiles/types checks; it never performs calculations or Lean verification.
**StatProof: Show Claims** opens the Explorer view for current claims,
requirements, assumptions, and matching evidence. Field completion preserves
optional evidence types. After edits, old evidence appears only as historical.

See the [editor guide](../../docs/editor.md) for setup, examples, isolated launch,
settings, tests, snapshot status, and current limitations. This extension is for
local development; it is not published to the Marketplace.
