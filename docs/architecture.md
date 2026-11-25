# Architecture

```text
.stat source → parser → typed plan + requirements
                           │
              ┌────────────┴──────────────┐
              │                          │
       LSP diagnostics             explicit execution
       completion, hover           Python exact arithmetic
       Claims inspection           the program as Lean data:
                                   contracts decided, claims proved
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
- `language_printer.py`: the canonical program printed back as source. It imports
  nothing from the compiler; compiling what it prints must give the same program.
- `language_fields.py`, `language_values.py`: public fields and runtime values.
- `language_runner.py`, `verification.py`: explicit execution and certificates.
- `methods/`: cited methods, outcomes, null forms and assumptions, all as data.
  The language builds their constructors and contracts from this registry.
- `composition.py`: families whose members are assumed and whose combination
  Lean checks.
- `lean_translation/` writes the canonical program and numerical hints as Lean data.
  `table.py` classifies the DSL constructors. `certificate.py` binds the source,
  program and reported values. `verification.py` builds, audits and replays the
  certificate, and `program_evidence.py` connects it to each verified request.
- `derivations.py`, `derivation_checker.py`, `contract_reports.py`: why a
  contract passed, an independent check of that, and the study report.
- `StatClaim/`: Lean definitions, theorems and composition rules.
  `StatClaim/Interface/` holds the objects the semantics is stated in: abstract
  two-arm and observational models, tests seen from outside and their level
  premises, and families over joint studies. `StatClaim/Generated/Methods.lean` is
  the cited-method registry in Lean, written by `scripts/update_lean_premises.py`,
  with the cited procedures that combine tests (`composition.CITED_RULES`): Lean has
  one constructor for all of them, `Test.procedure`.
  `StatClaim/Semantics/` defines each program's claims, premises, grades and
  contracts as functions of the encoded program; exact tests, results, intervals
  and plans share one interface (`Exact.lean`). `Program.sound` proves the claims
  after the kernel checks the contracts and hints. `Encode.lean` prints the data as
  a form whose objects list their keys in order, and `Injective.lean` proves that
  two programs in canonical form (`Program.Canonical`, decided in every build) never
  print the same form. The corpus check compares Lean's printed form with the
  canonical program and checks agreement with frozen
  statements written by the retired translator; `tests/lean/SemanticsReference.lean`
  states one example of each kind of claim and test independently. The rejection
  table asks Lean about programs Python rejects or leaves unresolved. All run with
  `make lean-check`.
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
- `looks_planning.py`: exact power of Fisher's test at interim looks, and searches over
  the looks' sizes (`look_search.py` lists the candidates).
- `methods/boundaries.py`: spending boundaries under the canonical joint distribution.
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
