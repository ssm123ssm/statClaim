# Contributing

StatProof needs statistical methods, Lean proofs, language/editor improvements,
and clear examples. Small documentation fixes are welcome. For a new method,
open an issue describing the model, null, assumptions and intended guarantee
before building it. See [adding modules](docs/adding-modules.md).

Priority areas include [sample-size/power planning and Bayesian adaptive
designs](docs/study-planning.md). Help define planning support alongside new
methods, with explicit assumptions and a clear distinction between proof,
numerical bounds and simulation results.

## Develop

Use Codespaces from the README, or install uv, elan and Node.js 22+:

```sh
make setup
npm --prefix extensions/vscode ci --ignore-scripts
make check
make editor-check
make catalogue-check repository-check
```

`make python-check` is the fast loop. `make check` also checks Lean and real
certificate replay. Editor integration tests open VS Code; Linux needs Xvfb.
See [development](docs/development.md) for details.

## Submit

1. Branch from `main`; keep changes focused.
2. Add meaningful tests, including rejected or unsupported inputs for new methods.
3. Update the catalogue, examples and relevant short docs.
4. Open a PR explaining the problem, behavior and checks run.

Never commit secrets, generated certificates, environments, agent instructions
or memory notes. Use explicit file paths when staging. Commit messages must not
include co-author or contributor trailers. Contributions use the MIT license.

Proof changes need review of the statement and assumptions as well as passing
Lean. Maintainers merge after required CI and review; authors should disclose
which checks they could not run. Be respectful; see [community rules](CODE_OF_CONDUCT.md).
