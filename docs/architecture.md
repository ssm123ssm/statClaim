# Architecture

```text
.stat source → parser → typed plan + requirements
                           │
              ┌────────────┴──────────────┐
              │                          │
       LSP diagnostics             explicit execution
       completion, hover           Python exact arithmetic
       Claims inspection           Lean theorem instantiation
                                   certificate + result fields
```

The compiler is written in Python. It does not continuously generate Python
source: it builds typed objects in memory. `use` loads registered constructors
from `src/statclaim/language/registry.py`, not arbitrary Python or `.stat` files.

- `language_syntax.py`: syntax and source spans.
- `language/`: typed objects (`ir.py`), their canonical JSON (`normalize.py`), the
  builders and checks by area (`designs`, `analyses`, `points`, `checks`, `searches`),
  the operations verify, calculate and simulate (`operations.py`), every module and
  constructor (`registry.py`) and elaboration (`elaborate.py`). Each imports only the
  ones before it in that list; the package re-exports its public names.
- `language_contracts.py`, `language_compiler.py`: compatibility and requirements.
- `language_fields.py`, `language_values.py`: public fields and runtime values.
- `language_runner.py`, `verification.py`: explicit execution and certificates.
- `methods/`: cited methods, outcomes, null forms and assumptions, all as data.
  The language builds their constructors and contracts from this registry.
- `composition.py`: families whose members are assumed and whose combination
  Lean checks.
- `lean_translation/`: the translation of whole programs to Lean
  ([proposal](proposals/lean-translation.md)). `table.py` says what each
  constructor and operation becomes in Lean; `denote.py` decides what a compiled
  program states (`exact.py` for exact tests, with their theorems in
  `statements.py`), `prove.py` how each statement is proved, and `grades.py` how a
  claim's grade follows from the premises its proof uses; `program.py` writes the
  file. `certificate.py` makes it a certificate, which `verification.py` builds,
  audits and replays, and `program_evidence.py` gives each verified claim of a run
  its evidence from it. `rejection.py` defers Python's contract checks so a refused
  program still reaches Lean. `scripts/check_lean_translation.py` and
  `scripts/check_lean_rejections.py` run both on the corpus in `make lean-check`.
- `derivations.py`, `derivation_checker.py`, `contract_reports.py`: why a
  contract passed, an independent check of that, and the study report.
- `StatClaim/`: Lean definitions, theorems and composition rules.
  `StatClaim/Interface/` holds the objects translated programs are stated in:
  abstract two-arm and observational models, tests seen from outside and their
  level premises, families over joint studies, the shape of a program's
  theorem, and the `statclaim` tactic. `StatClaim/Generated/Methods.lean` is
  the cited-method registry in Lean, written by `scripts/update_lean_premises.py`.
  `StatClaim/Semantics/` defines what a compiled program means, as Lean functions of
  the program as data ([proposal](proposals/lean-semantics.md)); certificates do not
  use it yet. `Soundness.lean` proves every covered claim from its premises once, for
  every program. `lean_translation/data.py` writes the data from the canonical program,
  and `scripts/check_lean_semantics.py` checks on the corpus that Lean's encoding of it
  is the canonical program, that its grades are Python's, and that today's translation
  states the same claims.
- `lsp.py`, `extensions/vscode/`: editor protocol and UI.
- `studio/`: the block editor. `api.py` answers its requests on the same compiler,
  runner and language-server features; `server.py` serves it on this machine, and
  the web studio runs it in the browser in Pyodide, without Lean.
- `catalogue.py`: classified public inventory generated from those registries.

Planning claims (`meets`, sample-size searches) are calculated, simulated or proved
in Lean. `plan_kinds.py` lists every kind of analysis a planning claim can be about,
with how its claims are checked, described, run and derived; the modules below do
the work:

- `planning.py`, `observational_planning.py`: exact power, checked in Lean.
- `cited_planning.py`, `association_planning.py`: formula or exact power for cited
  tests, from `methods/power.py` and `methods/association_power.py`.
- `precision.py`, `precision_planning.py`: margins of error and assurance.
- `looks_planning.py`: exact power of Fisher's test at interim looks.
- `simulation.py` (the seeded engine), `methods/simulation.py` (the models) and
  `simulated_planning.py`: power and Type I error by simulation.

Every numerical method is cross-checked against R by a script in
`replication/comparison/` that writes a fixture the tests read offline.

A result is `verified` (proved in Lean), `conditional` (the combination is
proved, the members are assumed) or `cited` (only the fit to a published
method's contract is checked). Cited results never start Lean.

Compilation can reject a wrong null or report a missing proof adapter. It cannot
predict every backend error or decide arbitrary theorems. Only successful Lean
checking creates evidence for the precise supported claim. See [scope](scope.md).
