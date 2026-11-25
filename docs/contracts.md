# Contract derivations

When you write `fisher(design=..., null=..., alpha=...)`, StatClaim checks that
the pieces fit: the null belongs to the design's model, the test supports that
kind of null, and the level is a probability. This is a **contract**.

A failed contract is a diagnostic, as before. A passing contract now keeps a
**derivation**: the rules applied, the facts each rule used, the assumptions
you must meet in the real study, and any obligation still open. Nothing is
shown unless you ask.

Each rule and contract has a version, recorded in the derivation.

A derivation is about compatibility. It does not prove an error rate or power.
Those are claims, established by `verify(...)` and Lean.

One exception is marked clearly. The contract of a [cited method](cited-methods.md)
carries the published guarantee it gives you, the assumptions it needs and its
references. The checker confirms this is the guarantee the declaration implies,
not that the guarantee is true. An open obligation withholds it.

## Ask why a contract passed

In VS Code, put the cursor on a declaration and run **StatClaim: Explain
Contract**. From a terminal:

```sh
uv run --locked statclaim explain examples/tutorial/01_first_claim.stat
```

```text
Conclusion: analysis: the design, the null and the level fit this analysis.

Why it passed
1. same-model: the null and the design describe the same study model.
2. supported-null: the declared null (p_treatment = p_control) is supported.
3. level-range: the level 1/20 is a probability.
4. analysis-contract (from steps 1, 2, 3)
5. fixed-sampling: sampling is fixed, as the fixed-sample error theorem requires.

Assumptions you must meet in the real study
- The two samples are independent, each with one common success probability.
- ...

Unresolved obligations: None.
Independent check of this derivation: passed.
```

The three lists mean different things:

| List | Meaning |
| --- | --- |
| Steps | Established from your declarations by a rule. |
| Assumptions | Facts about the real study that StatClaim cannot check. |
| Unresolved obligations | Something a later guarantee needs that is not yet shown, such as a fixed sample size or an alpha allocation within budget. |

## The independent checker

`derivation_checker.py` re-validates every derivation. It reads the facts again
from the serialized declaration, re-evaluates each premise with its own code,
and confirms that the steps, their order, the conclusion, the assumptions and
the open obligations are exactly what the declaration implies. It does not call
the contract code or the code that built the derivation. A rule name or a
success flag alone does not pass.

The rules are stated once, as data, in `derivations.py`. The checker is only as
good as those statements: a wrongly stated rule would be checked faithfully.

## Study report

```sh
uv run --locked statclaim report study.stat --output report.md
```

The report is written to be pasted into a statistical analysis plan. It gives
the strongest status each claim can receive (verified, conditional or cited),
whether each guarantee is exact or approximate, and one table of every
assumption with its kind, whether the file declares it, and the claims that
need it. It also lists every validated contract with its justification, the
assumptions to meet, outstanding obligations and requested claims. Add `--json`
for a structured version.

In a StatClaim checkout, `--lean` also encodes the program as Lean data and checks
it there:

```sh
uv run --locked statclaim report study.stat --lean
```

The report then opens with a Lean check: the contracts Lean decided, each claim
with the grade the semantics gives it (proved, conditional, cited or declared,
from the premises the claim rests on) beside Python's status, the claims whose
design supplies no sampling law, the claims left unresolved and why, and what
stays outside Lean. The check is a certificate of its own,
`statclaim_program_certificate`, which `check-certificate` replays. If Python
accepts the program and Lean does not, the report says so and exits with 1.

## What a change affects

```sh
uv run --locked statclaim impact before.stat after.stat
```

Derivations are recomputed for both versions. The result names the
declarations changed directly, those affected through a dependency, the
contracts whose derivation changed or disappeared, and the claims that must be
verified again. In VS Code, **StatClaim: Show Change Impact** compares your
unsaved edits with the file as last saved.

## Coverage

Derivations are recorded for named declarations of these kinds:

| Declaration | What its derivation shows |
| --- | --- |
| `fisher(...)`, `fisher_one_sided(...)`, `difference_test(...)` | The null, design and level fit; whether sampling is fixed. |
| `bonferroni(...)` | Each member fits, members are distinct, the allocation is within budget. |
| `binomial_test(...)` | The sample size, null rate and level are valid. |
| `two_stage_test(...)` | The stages, the decision rule and the null rate form a complete design. |
| `meets(...)`, `sample_size(...)`, `smallest_sample_size(...)` | The analysis fits, the planning point lies outside the null, and the target and search range are valid. |

An analysis written inline inside a planning claim is covered by that claim's
derivation. Models, designs, nulls and observations have no contract of their
own; their inputs are validated when they are declared.
