# StatProof in VS Code

The prototype provides live diagnostics, module/constructor/named-argument/field
completion, typed object completion, statistical hover explanations,
go-to-definition for local declarations, and a Claims view. Both the original command spelling and
first-class calls such as `let checked = verify(claim)` are supported.

## Start an extension development host

From the StatProof repository root, with Python 3.12/uv, Node 22 or later, and
VS Code installed:

```sh
uv sync --locked
npm --prefix extensions/vscode ci --ignore-scripts
code --new-window "$PWD"
```

In VS Code, choose **Run and Debug → StatProof Extension**, then press **F5**.
The repository's `.vscode/launch.json` starts a second window with this extension
loaded. Open `examples/first_class.stat`, `examples/fisher.stat`, or
`examples/two_outcomes.stat` in that window. No TypeScript build is needed.

Alternatively, launch a standalone development host with an isolated profile:

```sh
code --new-window --disable-extensions --disable-workspace-trust \
  --user-data-dir "$PWD/.statproof/vscode-development-profile" \
  --extensions-dir "$PWD/.statproof/vscode-development-extensions" \
  --extensionDevelopmentPath="$PWD/extensions/vscode" \
  "$PWD" "$PWD/examples/first_class.stat"
```

This is the same isolated setup used during initial development. The trust flag
applies to that dedicated development instance. It does not change global editor
settings or install the extension into the normal editor profile. Close the
development window to stop its language server. A server is launched per editor
host; there is no separate background service to start first.

If `.statproof/playground/` exists, its files are scratch copies created for
interactive testing. They are ignored by Git and are independent of the canonical
examples and test fixtures. Feel free to edit these while development continues.

## Try the editing features

1. Open `first_class.stat`. Hover `analysis`, `validity`, and `design_verification`.
   Hovering a claim shows its mathematical scope and required assumptions.
2. At the start of a scratch file type `use tests.` and invoke completion
   (**Ctrl+Space**, or **Cmd+Space** if configured that way). Select `tests.fisher`.
3. In a file with the model, plan, and null declarations, type
   `let next = fisher(`. Completion offers `design=`, `null=`, and `alpha=`.
   After `design=`, it suggests compatible in-scope designs and constructors.
4. Use **Go to Definition** on `plan` in `fisher(design=plan, ...)`. It selects
   the identifier in the original declaration.
5. Change an alpha to `2`. A syntax/type/domain error appears in Problems.
   Restore it and the obsolete diagnostic disappears.
6. Try `adaptive.stat` and `overallocated.stat`. Their known unmet requirements
   appear as warnings from **statproof requirements**, distinct from syntax/type
   errors. They do not establish that the requested guarantee is false.

Incomplete calls and lists can still use completion and hover for earlier valid
declarations. Constructors are offered only after their modules have been
imported. Expected-type filtering uses the existing constructor schemas; list
element refinements and more specific claim subtypes are not yet inferred.

Run **StatProof: Show Claims**, or expand **StatProof Claims** in the Explorer,
to inspect each claim, its requirements/assumptions, and matching explicit check
results. Old results move to a separate historical section after edits.
See [public fields and the Claims view](fields-and-claims.md) for the detailed
workflow, optional evidence semantics, and `examples/fields.stat`.

## Run verification explicitly

Open a file-backed `.stat` document and run **StatProof: Verify Current File** from
the Command Palette (**Cmd+Shift+P** on macOS). This saves the file and invokes:

```sh
uv run --locked statproof check /path/to/file.stat --project /path/to/statProof --json
```

The **StatProof** output channel retains the complete report and certificate
locations; the Claims view shows matching evidence. The status bar identifies the checked editor version, with the full
source SHA-256 in its tooltip. A successful `verified` status concerns the report's
listed claims under its assumptions. Inspect the per-request results for scope;
an unresolved request can coexist with a successful certificate for another.

Typing, saving, completion, hover, and definition lookup never execute numerical
calculations, Lean, or certificate issuance. The LSP uses only the backend-free
compiler. Hover information describes types and planned operations, rather than
claiming that a proof has executed. Proof results appear through the explicit
command's output and status bar.

Any edit marks the previous execution status **stale**, even a comment edit.
An edit during a running check cannot later be overwritten by a current
`verified` status. Old results and certificates still describe their recorded
snapshot. A second check of the same file cannot start until the first finishes.
Closing/reopening a document does not restore a proof status from a persistent
cache.

## Configure and iterate

The extension uses `uv` from the editor process's PATH. If VS Code was launched
from the Dock and cannot find it, put its absolute path in the workspace setting
`statproof.uvPath` (find it with `command -v uv`). `statproof.projectPath` can select
the StatProof repository when editing `.stat` files in another workspace.

By default the project is the first workspace folder containing
`src/statproof/language.py`, or the development extension's containing repository.
The initial implementation supports one StatProof backend project per host.

Run **StatProof: Restart Language Server** after Python server/compiler changes.
This clears the server's state, reopens the buffers, and marks prior proof status
stale. After extension JavaScript, manifest, or syntax grammar changes, run
**Developer: Reload Window** in the development host. Configuration changes also
require reloading. After backend/module changes, reverify the source; no library
file watcher automatically establishes new evidence.

## Validation

```sh
uv run --locked pytest tests/test_lsp.py
npm --prefix extensions/vscode run check
npm --prefix extensions/vscode run test:unit
npm --prefix extensions/vscode test
# Equivalent editor checks:
make editor-check
```

The Python tests cover protocol framing/lifecycle, subprocess stdio exchange,
document versions, diagnostics clearing, incomplete input, UTF-16 positions and
CRLF, completion, hover, definition lookup, and the absence of execution on the
editing path. The Node tests check syntax-highlighting patterns. The editor test
launches a real isolated VS Code host, exercises language features, runs an
explicit Lean verification, and checks stale status after and during editing.

The editor test uses an installed macOS VS Code when found. Set
`VSCODE_EXECUTABLE_PATH` to use another installed binary; otherwise the official
VS Code test runner downloads its test editor. Each run uses a separate temporary
profile, and its scratch files/results are under `.statproof/ide-test-*`.

The implementation follows the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
and uses Microsoft's [VS Code language client](https://github.com/microsoft/vscode-languageserver-node).
See the official [extension guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide)
and [test-host guide](https://code.visualstudio.com/api/working-with-extensions/testing-extension).

## Current limits

This is a local-file prototype: no cross-file user modules, constructor-source
definition lookup, rename/refactoring, semantic tokens, proof cancellation UI,
or persisted proof cache. Syntax coloring is TextMate-based. Completion is
conservative when an earlier declaration is malformed. Full-document analysis
runs synchronously on changes; there is no background proof work or proof-status
decoration attached to individual declarations. The server advertises full-text
synchronization, and also understands ranged changes for protocol tests/clients.
