# Adding an object or module

There is no external plugin loader yet. Modules are registered in the repository.
Start with an issue containing a small `.stat` example and the desired claim.

1. Define the model, hypothesis, design and assumptions precisely. Explain which
   combinations must fail and why.
2. Add a typed object/constructor in `language.py`. Add an analysis contract in
   `language_contracts.py`; never silently replace the user's null.
3. Publish fields through `language_fields.py`. Keep compilation pure: no Lean,
   calculations, filesystem writes or evidence generation while editing.
4. Add an explicit lowering/proof adapter and Lean theorem for supported claims.
   Unsupported claims must retain an unresolved requirement, never a verified flag.
5. Classify new modules and field-bearing types in `catalogue.py`. Run
   `uv run python scripts/update_catalogue.py` to refresh the reference.
6. Add tests: valid and mismatched nulls/models, invalid inputs, missing adapters,
   exact calculations, real Lean checks, certificate replay/tampering and LSP
   diagnostics. Add UI tests when result/evidence behavior changes.
7. Add a small example and update scope docs. Run the contributor checks.

Keep registry metadata, runtime behavior and formal statements aligned.
A maintainer reviews mathematical meaning and assumptions before merging.
