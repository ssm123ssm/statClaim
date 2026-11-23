# Programs from the StatClaim article

Each program the article shows, as a complete file. Every link opens the program
in the web studio, which runs everything except Lean proofs. For proofs, open the
same study in the [Codespace](https://codespaces.new/ssm123ssm/statClaim?quickstart=1)
or run `statclaim check` on the file.

| Article section | File | Result | Open in the web studio |
| --- | --- | --- | --- |
| Introduction | `fisher_design.stat` | `verified` Type I error bound | [paper/fisher_design](https://ssm123ssm.github.io/statClaim/?open=paper/fisher_design) |
| Introduction | `fisher_adaptive.stat` | `unresolved_obligation`: unspecified stopping | [paper/fisher_adaptive](https://ssm123ssm.github.io/statClaim/?open=paper/fisher_adaptive) |
| Composing models and naming claims | `composed_model.stat` | Declarations only | [paper/composed_model](https://ssm123ssm.github.io/statClaim/?open=paper/composed_model) |
| Composing models and naming claims | `fisher_observed.stat` | `verified` p-value for observed counts | [paper/fisher_observed](https://ssm123ssm.github.io/statClaim/?open=paper/fisher_observed) |
| Targets and candidate designs | `fisher_sample_size.stat` | `verified`: 36 per arm is the smallest size | [paper/fisher_sample_size](https://ssm123ssm.github.io/statClaim/?open=paper/fisher_sample_size) |
| Simulation and its uncertainty | `t_test_simulation.stat` | `calculated` and `simulated` power | [paper/t_test_simulation](https://ssm123ssm.github.io/statClaim/?open=paper/t_test_simulation) |
| Precision targets | `response_rate_precision.stat` | `calculated`: 89 participants | [paper/response_rate_precision](https://ssm123ssm.github.io/statClaim/?open=paper/response_rate_precision) |
| Rechecking Simon's two-stage designs | `simon_design.stat` | `verified` error and power bounds | [paper/simon_design](https://ssm123ssm.github.io/statClaim/?open=paper/simon_design) |
| Rechecking Simon's two-stage designs | `simon_search.stat` | Optimal and minimax designs, `calculated` | [paper/simon_search](https://ssm123ssm.github.io/statClaim/?open=paper/simon_search) |
| A COPD trial analysis plan | `replication/copd/design_cited.stat` | `cited` | [copd/design_cited](https://ssm123ssm.github.io/statClaim/?open=copd/design_cited) |
| A COPD trial analysis plan | `replication/copd/design_declared.stat` | `declared` | [copd/design_declared](https://ssm123ssm.github.io/statClaim/?open=copd/design_declared) |
| A COPD trial analysis plan | `replication/copd/power.stat` | `calculated` power statements | [copd/power](https://ssm123ssm.github.io/statClaim/?open=copd/power) |

The tutorial lessons have links too, such as
[tutorial/07_sample_size](https://ssm123ssm.github.io/statClaim/?open=tutorial/07_sample_size).

Each file's comments explain it; the studio shows them as the study's description
and as notes beside its blocks. These names are cited in the article, so do not
rename the files.
`tests/test_paper.py` checks the numbers the article reports, and
`replication/examples.py` checks every file's status, with `--lean` for the proofs.
