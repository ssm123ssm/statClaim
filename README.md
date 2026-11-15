# StatProof

A statistical language that checks whether a study, hypothesis and analysis fit
together, then uses Lean to verify supported mathematical claims.

[![Check](https://github.com/ssm123ssm/statProof/actions/workflows/check.yml/badge.svg)](https://github.com/ssm123ssm/statProof/actions/workflows/check.yml)
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/ssm123ssm/statProof)

**0.1 developer preview.** The supported Fisher subset has automated proof,
replay and editor tests. The language and APIs may change. This is a research
tool; a checked theorem establishes the stated mathematical claim under its
assumptions, not the quality of a real study.

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

While editing, the language server checks types, hypothesis compatibility and
proof requirements. **Verify Current File** explicitly runs calculations and
Lean. For example, replacing the null with a nonzero difference in proportions
produces guidance before execution.

## Try it

Open Codespaces above, wait for setup, then open `playground/welcome.stat`.
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
