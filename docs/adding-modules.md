# Adding an object or module

There is no external plugin loader yet. Modules are registered in the repository.
Start with an issue containing a small `.stat` example and the desired claim.

A method whose guarantee Lean cannot prove yet is added as a
[cited method](cited-methods.md) instead; step 4 does not apply to it.

1. Define the model, hypothesis, design and assumptions precisely. Explain which
   combinations must fail and why.
2. Add a typed object in `language/ir.py`, its builder in the module of its area
   (`designs`, `analyses`, `points`, `checks`, `searches`), and its constructor in
   `language/registry.py`. Add an analysis contract in `language_contracts.py`;
   never silently replace the user's null.
3. Publish fields through `language_fields.py`. Keep compilation pure: no Lean,
   calculations, filesystem writes or evidence generation while editing.
4. For claims Lean proves, give the object its meaning in `StatClaim/Semantics/`:
   a constructor in `Syntax.lean` with its encoding in `Encode.lean` (keys in
   increasing order, and its case in `Injective.lean`), its
   contracts in `Contracts.lean`, and its meaning in `Meaning.lean`, or through
   an `ExactModule` (`Exact.lean`) for an exact test, with result, interval and
   planning checks where they apply (`Results.lean`, `Intervals.lean`,
   `Plans.lean`). Write it
   from the canonical program in `lean_translation/data.py`, and its numerical
   hints in `lean_translation/material.py`. Add a reference statement to
   `tests/lean/SemanticsReference.lean`; a test fails if a constructor has none.
   Unsupported claims must retain an unresolved requirement, never a verified flag.
   Give each new assumption sentence an id and kind in `methods/identify.py`.
   Add any new diagnostic code, status or limit to `reference.py`; a test fails
   if a code is raised but not documented.
5. Classify new modules and field-bearing types in `catalogue.py`. Run
   `uv run python scripts/update_catalogue.py` to refresh the reference. Give each
   new constructor an entry in `lean_translation/table.py`: its role and the Lean
   files that give it meaning, or why it has none. A test fails otherwise.
6. Add tests: valid and mismatched nulls/models, invalid inputs, missing adapters,
   exact calculations, real Lean checks, certificate replay/tampering and LSP
   diagnostics. Add UI tests when result/evidence behavior changes.
7. Add a small example and update scope docs. Run the contributor checks.
8. For new tests and designs, propose sample-size and operating-characteristic
   support alongside the analysis where possible. State the planning inputs,
   target, applicable claims and evidence method; record unsupported planning
   explicitly. This is the [planning roadmap](study-planning.md), not an existing
   plugin API. Bayesian modules should also specify priors and decision criteria.

   A new kind of planned analysis is one entry in `plan_kinds.KINDS`. The entry names
   how `calculate`, `verify` and `simulate` are checked, how the claim is described,
   run and derived, and which record it publishes. Then teach the independent checker
   in `derivation_checker.py` to re-derive the new derivation from its JSON.

Keep registry metadata, runtime behavior and formal statements aligned.
A maintainer reviews mathematical meaning and assumptions before merging.
