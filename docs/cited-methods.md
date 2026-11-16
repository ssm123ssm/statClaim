# Cited methods

Some guarantees are not proved in Lean. For these methods StatClaim checks that
your study fits the method's contract, then restates the published guarantee with
its assumptions and references. The result has status `cited`, never `verified`.

```stat
use models.two_arm_continuous
use sampling
use tests.t

let study = two_arm_continuous(n_control=60, n_treatment=60)
let plan = fixed(model=study)
let null = equal_means(model=study)
let analysis = t_test(design=plan, null=null, alpha=1/20)
let checked = verify(typeI(analysis))
```

No Lean installation is needed to check this file. See `examples/t_test.stat`.

## What is checked

- The null fits the test: `equal_means` for a two-sided test,
  `mean_difference_at_most` for a one-sided or non-inferiority test.
- The null and the design are declared over the same model.
- The design is `fixed`. With `adaptive`, the claim stays unresolved.
- There are enough participants to estimate the variance.

## What is not checked

The assumptions and the guarantee itself. Read them in the report, or with
`checked.evidence.required_assumptions` and `checked.evidence.references`.

## Supported tests

| Test | Null | Guarantee | Assumes |
| --- | --- | --- | --- |
| `t_test` | `equal_means` | Exact level | Normal outcomes, equal variances |
| `t_test_one_sided` | `mean_difference_at_most` | Level at most alpha | Normal outcomes, equal variances |
| `welch_test` | `equal_means` | Large-sample approximation | Finite variances |
| `welch_test_one_sided` | `mean_difference_at_most` | Large-sample approximation | Finite variances |

All assume independent observations, fixed arm sizes and one analysis.
`claim.guarantee` is `finite_sample` for the pooled tests and `asymptotic` for
Welch. A file with any cited claim has overall status `cited`.

Cited tests cannot yet join a Bonferroni family or a planning search.

## Adding a cited method

Add a `CitedMethod` to `src/statclaim/cited.py` with its scope, assumptions and
references, and register its constructor in `language.py`. Each entry needs a
published source and statistical review: the entry is trusted, not proved.
