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

**0.1 developer preview.** Current proof support covers the specified fixed-sample
Fisher setting, its exact power at a planning point, two-endpoint Bonferroni
composition, the one-sample exact binomial test, and a two-stage binomial design
with an interim stop. The language
and APIs may change. A checked theorem establishes its stated claim under its assumptions;
whether a real study satisfies those assumptions still needs scientific judgment.
See [scope and trust](docs/scope.md).

## Plan a study

State the rates you expect and the power you need, then check a design or
search for a sufficient sample size:

```stat
let alternative = binomial_rates(p_control=1/10, p_treatment=2/5)
let target = power_target(at=alternative, minimum=4/5, maximum_typeI=1/20)
let candidates = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=40)
let sizing = verify(sample_size(candidates=candidates, target=target))
```

Lean recomputes the power of the selected design, so the recommendation carries
checked evidence with its assumptions. Adaptive designs are planned the same
way: a two-stage design with an interim stop, using count or Bayesian posterior
rules, has its Type I error and power checked for the complete policy.
See [planning a study](docs/planning.md).

## Where we are going

Next come assurance and precision targets, more tests and designs, and richer
Bayesian and adaptive policies, including checks that priors, decision rules
and stopping policies fit together. See the [roadmap](ROADMAP.md) and
[planning roadmap](docs/study-planning.md).

## Try it

Open Codespaces above, wait for setup, then open `playground/welcome.stat`
(or `playground/planning.stat` and `playground/two_stage.stat`).
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
