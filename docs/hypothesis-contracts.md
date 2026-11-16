# Hypothesis compatibility contracts

The one-sided analysis `fisher_one_sided` accepts
`proportion_difference_at_most(model=..., value=0)` and no other null; see
[planning](planning.md). The rest of this page describes the two-sided contract.

Language version `0.4.0` adds structured proportion-difference hypotheses and an
explicit hypothesis contract on the Fisher constructor. This supports the case
where the study/model is correct but the chosen analysis does not support the
declared null.

```text
use models.two_arm_binomial
use sampling
use tests.fisher

let study = two_arm_binomial(n_control=100, n_treatment=100)
let plan = fixed(model=study)
let null = proportion_difference(model=study, value=0.10)
let analysis = fisher(design=plan, null=null, alpha=0.05)
```

This is the scenario in `examples/hypothesis_mismatch.stat`. The compiler reports
`hypothesis_mismatch` at the analysis's `null` argument, without needing a call to
`verify`. The diagnostic shows:

- Declared null: `p_treatment - p_control = 1/10`.
- Supported null: `p_treatment = p_control`.
- Guidance to retain the declared null and select/implement a matching analysis,
  or use equality only if that is the intended statistical question.
- A related location at the original hypothesis declaration, including through
  aliases and projections of named hypotheses.

This means the current analysis/proof adapter does not support that null. It
does not prove that the null is false, or that no method could analyze it. The
checker never silently replaces a requested null with another one.

## The hypothesis objects

All three constructors are imported by `use models.two_arm_binomial`:

| Constructor | Parameter restriction |
| --- | --- |
| `equal_proportions(model)` | `p_treatment = p_control` |
| `proportion_difference(model, value)` | `p_treatment - p_control = value` |
| `proportion_difference_at_most(model, value)` | `p_treatment - p_control <= value` |

The difference is treatment minus control. Values are exact numbers in `[-1,1]`.
For example, `0.10` means an absolute difference of 10 percentage points, not a
relative increase of 10%. These are declarations of parameter restrictions;
declaring one does not assert its truth for a real study or its observed data.

Hypotheses expose `model`, `predicate`, `value`, and `statement` as public fields.
Hovering a hypothesis in VS Code shows its mathematical restriction. The compiler
keeps nonzero equality and inequality predicates distinct in normalized objects.

Exactly zero equality difference is an alias for equal proportions. Thus
`proportion_difference(study, 0)` is accepted by Fisher. Zero inequality difference
is different: `proportion_difference_at_most(study, 0)` includes parameters with
unequal probabilities, and remains unsupported by the current Fisher contract.
See `examples/hypothesis_zero.stat` and `examples/hypothesis_inequality.stat`.

The Lean binomial module defines `proportionDifference` and
`proportionDifferenceAtMost`. Its checked theorem
`proportionDifference_zero_iff` establishes the zero-equality equivalence; the
language canonicalizes that exact alias to the existing equality null. It does
not reuse Fisher's theorem for shifted or inequality nulls. A zero-alias
certificate has the same canonical mathematical inputs as the original Fisher
example, and is replayed by integration tests. The original source spelling and
its translation remain part of the existing application provenance boundary.

## Model compatibility versus hypothesis compatibility

An analysis first requires a hypothesis on its declared model. A different model
produces `model_mismatch`, with the two declared arm sizes in the explanation.
Matching this model does not imply that the hypothesis form is supported:
Fisher's current contract then requires equal proportions.

Model matching retains the prototype's structural comparison by declared arm
sizes. It is not a real-world cohort identity check or evidence of independence.
Adaptive stopping remains a separate unmet sampling-law requirement; a matching
hypothesis alone does not establish the full analysis guarantee.

## Try it in the IDE

Reload the development window to pick up compiler and extension changes. Open
`examples/hypothesis_mismatch.stat` or its `.statclaim/playground/` scratch copy.
The analysis should immediately receive the diagnostic above. In Problems, open
the related information to find the original null; the Claims view also exposes
the source diagnostic and declaration link. Hover `null` and `fisher` to compare
the declared restriction with the analysis's supported contract.

If equality is your intended question, change the value to `0` or use
`equal_proportions`. The diagnostic clears, but this is still analysis rather than
a proof. To request evidence, add `let checked = verify(typeI(analysis))` and run
**StatClaim: Verify Current File**. If the nonzero null is intended, retain it:
a corresponding analysis/calibration adapter and proof are not implemented in
this milestone.

```sh
# Expected: invalid, exit 2, hypothesis_mismatch, no Lean or artifact writes.
uv run --locked statclaim compile examples/hypothesis_mismatch.stat
uv run --locked statclaim check examples/hypothesis_mismatch.stat

# Expected: valid planned equality claim, no execution.
uv run --locked statclaim compile examples/hypothesis_zero.stat

# Explicitly check the equality guarantee through the exact zero alias.
uv run --locked statclaim check examples/hypothesis_zero.stat
```

## Implementation and limits

`language_contracts.py` defines declarative hypothesis contracts. A constructor
registers its contract with its typed argument schema. The common elaborator
checks it before constructing an analysis. The same metadata supplies hover
documentation and the `contracts` entries in `statclaim modules --json`; the LSP
does not duplicate these statistical rules. The Fisher analysis object also
guards its invariant so internal Python code cannot accidentally lower a shifted
null through the equality-only adapter.

These are explicit supported predicate forms, not a solver for arbitrary
mathematical equivalence. Only the documented zero-equality normalization is
performed automatically. New methods need their own contracts, adapters, and
formal guarantees. No new test procedure or shifted-null certificate is issued
by adding a hypothesis constructor.

Unit/protocol tests reject mismatches before calculation or Lean, preserve exact
values and declaration locations, and check the distinction between equality and
inequality at zero. Lean checks the definitions and equivalence theorem. The
VS Code test exercises live diagnostics, related locations, hover meanings, the
Claims view, and clearing the error after an explicitly compatible declaration.
Fixed Fisher test inputs live under `tests/fixtures/`, so edits to the public
Fisher example do not silently alter parser/protocol test scenarios.
