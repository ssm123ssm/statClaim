# Roadmap

## 0.1 developer preview

- Typed study, null, analysis, claim and result objects.
- Fisher equality-null contracts, exact calculations and Lean certificates.
- Two-endpoint Bonferroni composition under declared joint laws.
- VS Code diagnostics and Claims view, Codespaces and contributor checks.
- Classified catalogue and documented scope.
- Planning: exact Fisher power, target checks and a bounded sample-size search,
  with an optional smallest-in-range claim.
- Sampling policies with their own records; a two-stage binomial design with
  count or Beta-posterior rules and checked Type I error and power.
- One-sided exact binomial test for a single arm, with sample-size search.

## Next

1. Make sample size, power and related error claims part of study planning.
   Introduce planning support alongside new tests and designs where possible.
2. Support Bayesian analyses and adaptive sampling as core use cases, including
   compatibility among priors, likelihoods, decision rules and adaptation policies.
3. Add an analysis supporting a nonzero difference null, with its own theorem.
4. Improve claim explanations, result inspection and teaching examples.
5. Define module compatibility and a versioned public extension API.

### Sample size and power

Provide one guided workflow: declare the scientific question and planning
assumptions, choose a target, then evaluate or search for a suitable design.
Offer documented, overridable method presets; keep scientific inputs explicit.
The result should attach a sample-size justification and applicable error claims
to the exact study specification.

Power for the fixed-sample Fisher analysis and a bounded sample-size search are
implemented; see [planning](docs/planning.md). Grow toward assurance, precision targets and adaptive designs,
including expected and maximum sample size. A sample size that meets a target
and the smallest possible sample size are separate claims.

### Bayesian and adaptive designs

A two-stage binomial policy with Beta-posterior decision rules is implemented.
Next: extend the composite-null error bound from count rules to posterior rules,
formalize the Beta posterior, and add assurance. Extend to adaptive allocation, further interim analyses
and stopping policies—the compatibility problem that originally motivated
StatProof. Support Bayesian planning criteria and, when requested, separate
repeated-sampling error and power claims for the complete decision policy.

For complex designs, automate supported calculations and simulation, report
their uncertainty, and add formal guarantees as proof adapters become available.
Composing verified components must not silently certify the whole design's
power or error rate. See [planning and Bayesian design](docs/study-planning.md)
for the proposed contracts and implementation sequence. These are planned
capabilities, not features of the current preview.

## Before a stable 1.0

Document migration rules; test supported platforms and clean installs; have
independent statistical and proof review; keep proof assumptions visible;
verify negative cases and certificate tampering; agree which APIs are stable.
A preview release does not promise language compatibility.
