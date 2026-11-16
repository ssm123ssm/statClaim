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
from `src/statclaim/language.py`, not arbitrary Python or `.stat` files.

- `language_syntax.py`, `language.py`: syntax, typed objects and constructors.
- `language_contracts.py`, `language_compiler.py`: compatibility and requirements.
- `language_fields.py`, `language_values.py`: public fields and runtime values.
- `language_runner.py`, `verification.py`: explicit execution and certificates.
- `methods/`: cited methods, outcomes, null forms and assumptions, all as data.
  The language builds their constructors and contracts from this registry.
- `composition.py`: families whose members are assumed and whose combination
  Lean checks.
- `derivations.py`, `derivation_checker.py`, `contract_reports.py`: why a
  contract passed, an independent check of that, and the study report.
- `StatClaim/`: Lean definitions, theorems and composition rules.
- `lsp.py`, `extensions/vscode/`: editor protocol and UI.
- `catalogue.py`: classified public inventory generated from those registries.

A result is `verified` (proved in Lean), `conditional` (the combination is
proved, the members are assumed) or `cited` (only the fit to a published
method's contract is checked). Cited results never start Lean.

Compilation can reject a wrong null or report a missing proof adapter. It cannot
predict every backend error or decide arbitrary theorems. Only successful Lean
checking creates evidence for the precise supported claim. See [scope](scope.md).
