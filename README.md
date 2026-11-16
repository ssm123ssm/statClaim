# StatProof

**Check that a statistical guarantee applies to your study.**

StatProof helps researchers make study assumptions explicit, catch incompatible
analyses, and obtain machine-checked evidence for supported statistical claims.

[![Check](https://img.shields.io/github/actions/workflow/status/ssm123ssm/statProof/check.yml?branch=main&style=flat&label=Check&logo=github&logoColor=white)](https://github.com/ssm123ssm/statProof/actions/workflows/check.yml)
[![Open in GitHub Codespaces](https://img.shields.io/badge/Open_in_GitHub_Codespaces-24292f?style=flat&logo=github&logoColor=white)](https://codespaces.new/ssm123ssm/statProof)

## Why StatProof?

A correctly computed p-value does not, by itself, establish that a method answers
your intended question or that its error guarantee applies to your study design.
Those connections still need justification.

For example, a study might test ten outcomes and declare a finding if any has
`p < 0.05`. Every test can be calculated correctly, yet testing each outcome at
the 5% level does not by itself establish a 5% false-positive bound for the study
as a whole.

A test's 5% false-positive guarantee may also assume a fixed sample size and a
single planned analysis. If a researcher repeatedly checks the data and
stops when a result becomes significant, that guarantee does not automatically
apply to the whole procedure. The calculations can be correct while the study's
error-control claim still needs justification.

StatProof connects the study, hypothesis, analysis and claim so it can:

- Explain supported incompatibilities while you edit, before running an analysis.
- Show, on request, why a declaration passed its checks and what it still assumes.
- Check applicable mathematical guarantees using Lean's proof checker.
- Reuse checked guarantees, with required assumptions and replayable evidence attached.

### Alongside R and Python

Keep using R or Python for data preparation, modelling and visualization.
StatProof adds an explicit specification of the study and the guarantee you want
to establish. Its small `.stat` notation gives the checker precise objects to
reason about: models, hypotheses, analyses, claims and evidence.

Today, you write that specification separately. The preview does not inspect or
certify existing R or Python scripts. The aim is to make statistical justification
easier to inspect and reuse within a research workflow.

## A small example

Declare a fixed-sample study, choose the equality null, and request a Type I error
guarantee at a significance level of `1/20`:

```stat
use models.two_arm_binomial
use sampling
use tests.fisher

let study = two_arm_binomial(n_control=100, n_treatment=100)
let plan = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=plan, null=null, alpha=1/20)
let claim = typeI(analysis)
let verification = verify(claim)
let status = verification.status
let evidence = verification.evidence
```

Change the null to `proportion_difference(model=study, value=1/10)` and the editor
explains why the current Fisher contract cannot support it. The guidance preserves
your statistical question: changing the null to satisfy a method would change
what you are asking.

While editing, StatProof checks types, hypothesis compatibility and proof
requirements. **Verify Current File** explicitly runs the requested operations
and Lean checks. `verification.evidence` is present only after successful
verification; a valid specification alone is not a proof.

## What is supported

| You want to | Use | Checked by Lean |
| --- | --- | --- |
| Compare two proportions | `tests.fisher` | Type I error, exact p-value and decision |
| Test one proportion | `tests.binomial` | Type I error, exact p-value and decision |
| Estimate one proportion | `tests.binomial` | Coverage of the exact confidence interval |
| Estimate a difference | `estimation` | Coverage of a conservative interval |
| Test several endpoints | `multiplicity.bonferroni` | Familywise error, 2 to 20 endpoints |
| Choose a sample size | `planning` | Power, and the smallest size in a range |
| Stop early for futility | `designs.two_stage` | Type I error and power of the whole design, and the decision for observed data |
| Find a two-stage design | `designs.two_stage` | The selected optimal or minimax design |

This is a 0.1 developer preview; the language and APIs may change. A checked
claim holds under its stated assumptions. Whether a real study meets those
assumptions is a scientific judgment. See [scope and trust](docs/scope.md).

## Plan a study

State the rates you expect and the power you need, then search for a sample size:

```stat
let alternative = binomial_rates(p_control=1/10, p_treatment=2/5)
let target = power_target(at=alternative, minimum=4/5, maximum_typeI=1/20)
let candidates = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=40)
let sizing = verify(smallest_sample_size(candidates=candidates, target=target))
```

The answer is 36 per arm. Lean recomputes the power of that design and checks
that no smaller size in the range reaches the target. Two-stage designs with
count or Bayesian posterior stopping rules are planned the same way.
See [planning a study](docs/planning.md).

## Where we are going

Assurance and precision targets, more tests and designs, and richer Bayesian
and adaptive designs. See the [roadmap](ROADMAP.md).

## Try it

Open Codespaces above, wait for setup, then open `playground/welcome.stat`.
The other files in `playground/` show planning, single-arm and two-stage studies.
Use **StatProof: Show Claims** and **StatProof: Verify Current File** in the
command palette. Your GitHub account controls Codespaces quota and billing.

Locally, install [uv](https://docs.astral.sh/uv/getting-started/installation/),
[elan](https://github.com/leanprover/elan#installation) and Node.js 22 or newer:

```sh
make setup
uv run --locked statproof compile examples/fisher.stat
uv run --locked statproof check examples/fisher.stat
uv run --locked statproof catalogue
```

See [quickstart](docs/quickstart.md) for VS Code and result inspection.

Then work through the [tutorial](docs/tutorial.html): ten lessons, from a first
checked claim to planning and analysing a study. Open the file in a browser;
the lesson files are in `examples/tutorial/`.

## Explore and contribute

- [Object and module catalogue](docs/catalogue.md): classifications, constructors and fields.
- [Architecture](docs/architecture.md): source, compiler, Python execution and Lean.
- [Scope and trust](docs/scope.md): what is checked and what remains an assumption.
- [Contributing](CONTRIBUTING.md): setup, tests and useful first contributions.
- [Adding a module](docs/adding-modules.md): implementation and testing checklist.
- [Roadmap](ROADMAP.md): priorities and release criteria.
- [Technical reference](docs/README.md): language, proofs and certificates.

Questions and proposals belong in [Discussions](https://github.com/ssm123ssm/statProof/discussions);
bugs and concrete tasks belong in [Issues](https://github.com/ssm123ssm/statProof/issues).
[MIT license](LICENSE).
