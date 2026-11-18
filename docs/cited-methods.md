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
  `mean_difference_at_most` for a one-sided or non-inferiority test, or
  `mean_difference_at_least` where lower values are better.
- The null and the design are declared over the same model.
- The design is `fixed`. With `adaptive`, the claim stays unresolved.
- There are enough participants to estimate the variance.

## What is not checked

The guarantee itself, and most of its assumptions. The report names each
assumption and marks it:

- `declared`: your file states it. `fixed` says the sizes are set in advance.
- `assumed`: nothing in the file can show it, such as normal outcomes.

Read them with `checked.evidence.required_assumptions` and
`checked.evidence.references`. The JSON report also gives each assumption's id
and kind, and the method's version.

The claim's guarantee is a structured value, not only a sentence:

```stat
let bound = checked.claim.guarantee.bound        # 1/20
let relation = checked.claim.guarantee.relation  # equals or at_most
let scope = checked.claim.scope                  # finite_sample or asymptotic
```

## Supported tests

| Test | Null | Guarantee | Assumes | Power |
| --- | --- | --- | --- | --- |
| `t_test` | `equal_means` | Exact level | Normal outcomes, equal variances | Two means |
| `t_test_one_sided` | `mean_difference_at_most` or `_at_least` | Level at most alpha | Normal outcomes, equal variances | Two means |
| `welch_test` | `equal_means` | Large-sample approximation | Finite variances | Two means |
| `welch_test_one_sided` | `mean_difference_at_most` or `_at_least` | Large-sample approximation | Finite variances | Two means |
| `log_rank` | `equal_survival` | Large-sample approximation, in the number of events | Independent censoring | Schoenfeld |
| `mmrm_test`, `mmrm_test_one_sided` | `equal_means`, `mean_difference_at_most` or `_at_least` | Large-sample approximation | Missing at random; correct mean and covariance model | Two means |
| `logistic_regression`, `logistic_regression_one_sided` | `equal_proportions`, a zero difference | Large-sample approximation | Linear log odds; enough events | Two proportions |

The t-tests are in `tests.t`, for `models.two_arm_continuous`. The log-rank test
is in `tests.survival`, for `models.two_arm_survival`; see `examples/log_rank.stat`.
Proportional hazards is not among its assumptions: the error rate does not need
it, though power does.

The mixed-model tests are in `tests.mixed_model` and test a treatment contrast,
such as the mean difference over all visits. The logistic tests are in
`tests.logistic` and use `models.two_arm_binomial`; the one-sided test supports a
zero difference only. See `examples/trial_models.stat`.

All assume independent participants, a plan fixed in advance and one analysis.

## Which direction is better

A one-sided null takes a side. `mean_difference_at_most` asks whether the
treatment's outcome is higher; `mean_difference_at_least` asks whether it is
lower. Say which direction is better on the model, and StatClaim checks that the
null faces the same way:

```stat
let study = two_arm_continuous(n_control=400, n_treatment=400, better="lower")
let symptoms = mmrm_test_one_sided(
    design=fixed(model=study),
    null=mean_difference_at_least(model=study, value=1/10),
    alpha=1/40,
)
```

Here `mean_difference_at_most` would be refused with `direction_mismatch`. If you
leave `better` out, the result lists the direction among its assumptions, as
`higher_is_better` or `lower_is_better`, marked assumed.
See `examples/lower_is_better.stat`.

For a yes-or-no outcome, every one-sided null asks whether the treatment's rate
is higher. Where a lower rate is better, as for death, state the complementary
outcome instead, such as alive. `better="lower"` with a one-sided binary null is
refused with that advice.

## Declared tests

When no entry fits, name the test yourself:

```stat
use tests.declared
let pain = declared_test(
    design=plan,
    null=equal_means(model=study),
    alpha=1/40,
    method="Van Elteren stratified rank test, stratified by site",
    reference="Statistical analysis plan, section 9.2",
)
```

StatClaim checks that the null and the design describe the same model, and
nothing about the test's guarantee. The result has status `declared`, the
weakest, and any result or file that contains the test names it as its weakest
part. `scope` is `asymptotic` unless you state `"finite_sample"`.
`claim.guarantee` is `finite_sample` for the pooled tests and `asymptotic` for
Welch. A file with any cited claim has overall status `cited`.

A way of combining tests can be cited too: see graphical procedures in
[multiple testing](multiple-testing.md#graphical-procedures).

Cited tests can join a Bonferroni family; see
[multiple testing](multiple-testing.md#families-with-cited-tests). The Power column
names each test's approximate power formula. Power is calculated only, never
verified; see [power for cited tests](planning.md#power-for-cited-tests).

## Adding a cited method

You need to read three short files, all in `src/statclaim/methods/`:

- `core.py`: what an assumption, a guarantee and a method are.
- `assumptions.py`: the shared assumptions. Reuse one before adding one.
- `t_tests.py`: a complete example to copy.

To add a test over an existing model and null:

1. Write a method file that exports `MODULE`, or add a `CitedMethod` to an
   existing file. State the null it supports, whether the error rate `equals`
   alpha or is `at_most` alpha, the scope, the assumptions and the references.
2. List a new file in `methods/__init__.py`.
3. Run `uv run python scripts/update_method_versions.py` and
   `uv run python scripts/update_catalogue.py`.
4. Add an example, and a test for a null the method must reject.

The constructor, its contract and guidance, editor support, catalogue entry,
derivation and report all follow from the entry.

To give a test approximate power, set its `power` to a `PowerFormula` from
`methods/power.py`, or add one there: a function of the planning point, the arm
sizes, the null's value, alpha and the sidedness, with its own assumptions,
references and version. A formula is versioned separately from the test, since
the test's error guarantee does not depend on it.

A new kind of endpoint is also data. Add an `Outcome` with its null forms to
`methods/outcomes.py`, as `SURVIVAL` does. Its model and null constructors then
exist in `.stat` files. `survival.py` is the complete example. Outcomes that
need more than two arm sizes to describe, such as covariates, are not covered
yet; open an issue first.

Each entry is trusted, not proved, so it needs a published source and statistical
review. After a reviewed change to an entry, raise its `version`. A test fails
until you do, because evidence records the version it relied on.
