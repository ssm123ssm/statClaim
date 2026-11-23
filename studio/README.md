# StatClaim Studio

A block editor for `.stat` studies, in the style of Scratch. From the repository root, run `.venv/bin/python studio/server.py` and open `http://127.0.0.1:4180/`. Restart the server after changes to `server.py` or `api.py`. Use `--port` to choose another port, and `--no-lean` to try it as the web studio runs, without Lean.

## Using it

- **New study** starts from a design: every design the language supports is a card, in five families. Search finds a card by its words (*cluster*, *interim*, *survey*), and so does `⌘K`. Then one question per step, while the study's blocks stack up beside them. Cards and tests show what their guarantee rests on; **Also** adds a sample size or the analysis of results where supported. **Create study** waits until StatClaim compiles the study. **Start empty** gives a blank file, whose canvas offers the families too.
- **Palette** (left). Pick a category on the rail, or press `/` to search. Click a block, then click a glowing input or **New value**, or press `Tab` and `Enter`. You can also drag it.
- **Colours and connectors** show types. A block's colour and the connector on its left edge show the type it makes: round for a study model, square for a design, pointed for a null, bevelled for an analysis, double for a multiplicity family, notched for a claim, zigzag for data, stepped for planning and a bracket for a list. An empty input shows the connector it takes, and palette blocks show the connectors of their inputs. Numbers and text are plain ovals.
- **Hints.** Select a stack, or click a palette block, and the palette shows what takes its value: those blocks glow with the input that takes it marked, and the rest fade. A dashed block takes it through another block, such as a t-test through a design. The rail counts them, **Show only these** hides the rest, and open inputs on the canvas that take it are ringed. StatClaim finds them by building each block with the value, so a continuous study hints the t-tests but not Fisher's test. `Esc`, empty canvas or ✕ ends the hints.
- **Dragging.** What you drag follows the pointer as a block, with mouse, pen or touch, and snaps to the nearest input that takes it. An input that does not take it says why. Dropped where nothing takes it, it flies back.
- **Canvas** (centre). Each `let` is a stack, with what it says in words underneath. Click a number to type, or drag it left or right to change it: whole numbers by one (`Shift` for ten), levels along 1/1000, 1/200, 1/100, 1/50, 1/40, 1/20, 1/10, 3/20 and 1/5, and rates by hundredths, kept as fractions. `Esc` puts it back. Click a dropdown to pick an option, or a value to replace it. A level also shows as a percentage; whole numbers step with − and + or the arrow keys. Click a block's name for more options. The **⋯** menu renames, adds a note, duplicates, reorders the file, explains why an analysis fits, collapses or deletes. Notes are `#` comments above a value, and the comment that opens the file is the study's description. Wrapped comment lines read as one paragraph; a bare `#` line starts the next.
- **Placing stacks.** Drag a stack by its hat, title or background to put it anywhere; drop it on the palette to delete it. Positions are kept per study in this browser, not in the `.stat` file. **Arrange by flow** puts each value to the right of what it uses; **Clean up** returns to one column in file order; **Zoom to fit** shows the whole study. The minimap appears when the study does not fit.
- **Moving values.** Drag a block or value out of its input to move it: onto another glowing input, onto empty canvas to make it a value of its own, or onto the palette to remove it. Hold `⌥` to copy instead. Dragging a stack's name always copies it. From the keyboard, choose **Move to another input…**, then `Tab` and `Enter`. To empty an input in place, press `Delete` on it or choose **Empty this input**.
- **Problems.** StatClaim checks every edit. Each empty input and error is listed once; values that fail only because they use a broken one wait quietly under its card. While there are problems, the run button reads **Fill 2 inputs** or **Fix 1 error** and leads to them; `F8` and `⇧F8` do the same. Open obligations are amber.
- **Run checks** (`⌘↵`) runs every `verify` and `calculate`, as `statclaim check` does, building Lean proofs where they exist. Each check block then shows its grade and what the run found, such as *Power 72.6% at n = 25, below the 80% target*. A claim is never shown as stronger than its weakest part. A check Lean certified wears a gold medal on its block, stamped on when the run finishes; it turns grey once the study changes, and click it for the result. Combinations with assumed members, cited tests, calculations and simulations get none. Values read from a result, such as `recommendation.calculation.n`, show their value at the end of their block. **Why?** shows the checked contract derivation: the steps, the assumptions to meet and what is not established. The **Results** tab shows each check under its block's hat, with the numbers, what was established, assumptions, references, certificates and the values the run filled in. Runs are written to `.statclaim/programs/`.
- **Simulation.** A `simulate` block estimates a t-test's power from simulated studies: its tray shows the estimate with a 95% interval, and a size search draws power by size in Results, with a table. The dice beside the seed tries another seed. Simulated results are estimates, never evidence.
- **After a run, drag a number** and the calculations and simulations rerun at once, without Lean, so values follow the edit. Proofs and cited checks keep their last results, marked outdated, until you run again. A typed edit marks everything outdated.
- **Fixes.** When an analysis's contract does not cover the declared null, Problems and the block's badge offer analyses that do. Changing the null is never offered, because it changes the question.
- **Practice this lesson** empties the links between a lesson's values. A checklist ticks off each one as you reconnect it, with a hint and the answer if you want them.
- **Code, Help** (right). Code shows the source with highlighting, completion as you type (or `Ctrl+Space`), hover help, and marks lines changed since the original or the last save. Help describes the block under the pointer.
- **Keyboard.** `⌘K` opens the command palette. Tab to a stack, then use the arrows to move between stacks, `⌥` and arrows to move it, `Enter` for its menu, `F2` to rename and `Delete` to remove it. `⌘Z`/`⇧⌘Z` undo and redo edits and moves; the clock button lists recent edits by name.

## Links

Every shipped study has a link: the web studio's address with `?open=` and the study's name, such as <https://ssm123ssm.github.io/statClaim/?open=paper/simon_design>. Names are `tutorial/<file>`, `example/<file>`, `paper/<file>` for the programs in the StatClaim article ([`examples/paper/`](../examples/paper/README.md)), and `<folder>/<file>` for a study in `replication/<folder>/`, such as the COPD case study's `copd/power`. The file's path in the repository works too. The address bar shows the open study's link, and **Copy link to this study** in `⌘K` copies its web-studio link. A link opens your edited copy if you have one; **Restore original** shows the study as shipped.

## Saving

In Chrome and Edge, **Save** (`⌘S`) writes to the file you opened, or asks where to save the first time; `⇧⌘S` saves as a new file. A tutorial saved to a file moves to **My studies**, and the tutorial keeps its original. Other browsers download the file. Unsaved edits are kept in this browser, even after closing the tab. **Restore original** discards edits to a tutorial or example.

## How it works

`api.py` answers every request the page makes, and `server.py` serves the files and that API over HTTP. The API is built on the StatClaim registry: modules, signatures, object fields, accepted input types and fixed choices. It compiles every edit, reads each value in words, explains contracts through `contract_reports.explain`, runs checks on request through `language_runner.check_source`, and answers completion and hover with the language server's features. It finds the blocks that take a value by building each one with it and simple numbers. Every edit patches the original source through the parser's spans, then the same compiler as the DSL checks it.

Where Lean is not available (the web studio, a checkout before `make setup`, or `--no-lean`), checks whose operation builds a proof, as `OPERATION_BACKENDS` in the language says, report **Needs Lean** and everything else runs as usual. The top bar says so before anything runs, and each such check offers **Get a proof**: the full studio in a Codespace, or StatClaim installed with Lean.

- `editor.js` runs the shell: documents, drafts, saving, checking, problems, practice, code and help.
- `palette.js` builds the categorised block palette.
- `document.js` draws the canvas, performs every edit and handles dragging.
- `designs.js` lists every design and builds its source; `wizard.js` is the new-study dialog.
- `ui.js` holds shared helpers, icons, connector shapes and the type colours.

The server listens on `127.0.0.1` only, serves only the editor's own files, and answers API requests only when they are JSON from a page on `127.0.0.1` or `localhost`, so other websites cannot start runs.

## The web studio

The same studio runs on GitHub Pages with StatClaim inside the browser, in [Pyodide](https://pyodide.org). `backend.js` is the page's only way to the API: on this machine it calls `server.py`; in the web studio it sends requests to `worker.js`, which starts StatClaim and `api.py` through `python.js`, and it reads the answers that never change, such as the block manifest and the lessons, from files. Lean cannot run in a browser, so proofs there say **Needs Lean**, as above. Codespaces runs the full studio with Lean: `.devcontainer/studio.sh` starts it when the Codespace starts and checks again when the editor connects, which forwards port 4180 and opens it in a tab. If the browser blocks the tab, open it from the globe beside port 4180 in the Ports panel. Each start is logged in `.statclaim/studio.log`.

`make site` builds the web studio into `dist/studio-site`; preview it with `python3 -m http.server --directory dist/studio-site`. CI builds it on every change, runs every example and lesson in its Pyodide and compares the answers with CPython's (`make site-check`), and publishes it from `main` once every check passes.

What keeps the two studios in step:

- One API. Add an endpoint to `api.GETS` or `api.POSTS` and both studios answer it; the build writes every GET answer into the site. Never answer a request in `server.py` alone.
- One file list. A new page file goes in `api.ASSETS`, which both the server and the build use; a test checks that every module the pages import is listed.
- Every operation says whether it needs Lean, in `OPERATION_BACKENDS`; a test requires it.
- What a request runs must work in a browser: no threads, subprocesses or network, and StatClaim keeps no dependencies outside Python's standard library. `make site-check` fails otherwise.

## Tests

Run `.venv/bin/python -m pytest tests/test_studio.py` for the backend, `make studio-check` for the DOM integration tests, which use the real server handlers in memory, and `make site-check` for the web studio. CI runs all three.
