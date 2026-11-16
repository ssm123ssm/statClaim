# Roadmap

## 0.1 developer preview

- Typed study, null, analysis, claim and result objects.
- Fisher equality-null contracts, exact calculations and Lean certificates.
- One-sided Fisher test with an error bound over "treatment no better than control".
- Exact test with a margin (non-inferiority), up to 120 participants per arm.
- Bonferroni composition of two to twenty endpoints under declared joint laws.
- VS Code diagnostics and Claims view, Codespaces and contributor checks.
- Classified catalogue and documented scope.
- Contract derivations with an independent checker, study reports and change impact,
  for analyses, families, one-sample tests, two-stage designs and planning claims.
- Planning: exact Fisher power, target checks and a bounded sample-size search,
  with an optional smallest-in-range claim and unequal allocation.
- Sampling policies with their own records; a two-stage binomial design with
  count or Beta-posterior rules and checked Type I error and power.
- One-sided exact binomial test for a single arm: sample-size search and
  checked p-values for observed data.
- Exact confidence intervals for one proportion with checked coverage, and a
  conservative interval for a difference of two proportions.
- Search for optimal or minimax two-stage designs; the selected design is checked.
- Checked decisions for observed two-stage data.

## Next

1. One-sided analyses in Bonferroni families.
2. A narrower exact interval for a difference of two proportions.
3. Larger sample sizes and p-values for the test with a margin.
4. Assurance and precision targets for planning.
5. More adaptive designs: several interim looks, efficacy stopping, allocation.
6. A formalized Beta posterior, so posterior rules need no stated closed form.
7. A versioned extension API for community modules.

Planning principles: scientific inputs stay explicit; a sufficient sample size
and the smallest one are separate claims; composing verified parts never
certifies a whole design by itself. Calculations, simulations and proofs stay
distinguishable in every report. See the [planning roadmap](docs/study-planning.md).

## Before a stable 1.0

Document migration rules; test supported platforms and clean installs; have
independent statistical and proof review; keep proof assumptions visible;
verify negative cases and certificate tampering; agree which APIs are stable.
A preview release does not promise language compatibility.
