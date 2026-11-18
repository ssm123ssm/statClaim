# Case study: a confirmatory COPD trial

The statistical analysis plan of study D5970C00002 (NCT03162055), edition 2.0,
8 June 2018, encoded in StatClaim. The trial compares glycopyrronium/formoterol
(GFF) with umeclidinium/vilanterol (UV) in COPD. Section numbers in the files
refer to that plan, which is not included here.

| File | What it encodes | File status |
| --- | --- | --- |
| `design_cited.stat` | The plan's analyses as it names them: mixed models for repeated measures and a logistic regression, as cited tests | `cited` |
| `design_declared.stat` | The same plan, each analysis declared by name with the plan's section as its reference | `declared` |
| `power.stat` | The four power statements of section 1.3 | `calculated` |

Each has its pinned output beside it: `*_check.txt` from `statclaim check`, and
`*_report.md` from `statclaim report`.

```sh
uv run python replication/copd.py --check          # reports and power; no Lean
uv run python replication/copd.py --lean --check   # every claim; needs Lean, about 20 s
```

## What the plan contains, and how it is encoded

- Two arms of 500, about 440 per arm in the per-protocol set; no interim analysis.
- Three co-primary hypotheses at one-sided 2.5%, starting with 1.25% each on the
  two non-inferiority tests, with recycling: `graphical`, status `cited`.
- If all three are rejected, four secondary endpoints in a fixed order at 2.5%:
  `fixed_sequence` with the graph as its first entry. Lean proves this
  combination; the tests are assumed, so its status is `conditional`.
- A file reports the weakest part anywhere in it, so the conditional sequence
  does not make the file look stronger than its cited or declared tests.

## Power statements

| Statement | Power | Estimate must exceed |
| --- | --- | --- |
| Trough FEV1 non-inferiority at 2.5% ("around 94%", "above -28 mL") | 0.9444 | -27.93 |
| Trough FEV1 non-inferiority at 1.25% ("90%", "above -24.5 mL") | 0.9051 | -24.76 |
| Peak FEV1 superiority at 1.25% ("at least 97%") | 0.9752 | 26.65 |
| TDI non-inferiority with margin -0.75 ("at least 90%") | 0.9598 at 2.5% | -0.354 |

All agree with the plan to rounding except the second critical value, 0.26 mL
from the plan's -24.5. A t quantile with 878 degrees of freedom gives -24.72, so
the difference does not come from the t distribution.

The plan's effective SD of 167 mL is 200 × √((1 + 3 × 0.6)/4): an equal-weight
average of four post-baseline visits with SD 200 mL and correlation 0.6 between
every pair (compound symmetry). The analysis itself uses an unstructured
covariance, so the power rests on an assumption the analysis does not make.

## Limits

- The models' covariates, covariance structure and fallback order are not
  encoded; the cited entries state a mixed model's assumptions in general.
- The analysis sets appear only as arm sizes.
- The superiority tests the plan runs after non-inferiority without gating the
  sequence are not encoded.
- The EMSCI margin is encoded as written: non-inferiority if the lower bound
  exceeds -0.1. The plan does not say which direction of this symptom score is
  better, so the report lists `higher_is_better` as assumed.
- Whether the protocol agrees with the plan was not checked, and the trial's
  results were not consulted.
