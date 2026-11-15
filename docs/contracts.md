# Contract derivations

When you write `fisher(design=..., null=..., alpha=...)`, StatProof checks that
the pieces fit: the null belongs to the design's model, the test supports that
kind of null, and the level is a probability. This is a **contract**.

A failed contract is a diagnostic, as before. A passing contract now keeps a
**derivation**: the rules applied, the facts each rule used, the assumptions
you must meet in the real study, and any obligation still open. Nothing is
shown unless you ask.

A derivation is about compatibility only. It does not prove an error rate or
power. Those are claims, established by `verify(...)` and Lean.

## Ask why a contract passed

In VS Code, put the cursor on a declaration and run **StatProof: Explain
Contract**. From a terminal:

```sh
uv run --locked statproof explain examples/tutorial/01_first_claim.stat
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
| Assumptions | Facts about the real study that StatProof cannot check. |
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
uv run --locked statproof report study.stat --output report.md
```

The report lists every validated contract with its justification, the
assumptions to meet, outstanding obligations and requested claims. Add `--json`
for a structured version.

## What a change affects

```sh
uv run --locked statproof impact before.stat after.stat
```

Derivations are recomputed for both versions. The result names the
declarations changed directly, those affected through a dependency, the
contracts whose derivation changed or disappeared, and the claims that must be
verified again. In VS Code, **StatProof: Show Change Impact** compares your
unsaved edits with the file as last saved.

## Coverage

Derivations exist for the Fisher analysis contract and the Bonferroni family
contract. Planning targets, one-sample tests and two-stage designs validate
their inputs but do not yet record derivations.
