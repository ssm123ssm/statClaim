# Study contract report

Source: `replication/copd/design_declared.stat`

Compilation status: `elaborated`

This report covers compatibility of the declarations. It is not a proof of any statistical guarantee. Claims below are established only by `verify(...)`.

Even a verified claim concerns the study as declared in this file, under the listed assumptions. It says nothing about how the study is run: an endpoint chosen after seeing data, participants excluded after randomisation, or repeated measurements counted as separate participants are invisible unless declared.

## Summary

| Declaration | Contract | Unresolved obligations | Independently checked |
| --- | --- | --- | --- |
| `trough_fev1_ni` | `tests.declared/declared_test` | 0 | yes |
| `peak_fev1_ni` | `tests.declared/declared_test` | 0 | yes |
| `peak_fev1_sup` | `tests.declared/declared_test` | 0 | yes |
| `co_primary` | `multiplicity.graphical/graphical` | 0 | yes |
| `inspiratory_capacity_ni` | `tests.declared/declared_test` | 0 | yes |
| `onset_of_action_sup` | `tests.declared/declared_test` | 0 | yes |
| `tdi_ni` | `tests.declared/declared_test` | 0 | yes |
| `emsci_ni` | `tests.declared/declared_test` | 0 | yes |
| `trial` | `multiplicity.fixed_sequence/fixed_sequence` | 0 | yes |

## Evidence each claim can receive

The strongest status `verify(...)` can give each claim. Nothing was run for this report.

| Claim | Kind | Best status | Weakest part | Exact or approximate |
| --- | --- | --- | --- | --- |
| `familywise(co_primary)` | familywise | cited: cited from the literature; not machine-checked | declared: trough_fev1_ni, peak_fev1_ni, peak_fev1_sup | large-sample approximation |
| `familywise(trial)` | familywise | conditional: combination proved in Lean; members assumed | declared: trough_fev1_ni, peak_fev1_ni, peak_fev1_sup, inspiratory_capacity_ni, onset_of_action_sup, tdi_ni, emsci_ni | large-sample approximation |

## Assumptions to meet in the real study

Declared: stated by this file. Assumed: nothing in the file can show it. Condition: says what the claim is about.

| Assumption | Kind | Status | Needed by |
| --- | --- | --- | --- |
| The tests, their starting shares of the level and the rules for passing a share on are fixed in advance, and a share is passed on only after a rejection. Each test controls its error at every level up to the overall level, not only at one. | design | declared | familywise(co_primary), familywise(trial) |
| trough_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited) | member | assumed | familywise(co_primary), familywise(trial) |
| peak_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited) | member | assumed | familywise(co_primary), familywise(trial) |
| peak_fev1_sup: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= 0. (declared by the author; not checked and not cited) | member | assumed | familywise(co_primary), familywise(trial) |
| The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test. | vouched | assumed | familywise(co_primary), familywise(trial) |
| Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked. | meaning | assumed | familywise(co_primary), familywise(trial) |
| The tests and their order are fixed in advance, and a test is carried out only if every earlier test in the order rejected. | design | declared | familywise(trial) |
| co_primary: Probability of rejecting any true member null is at most 1/40 whenever any subset of the member nulls is true. (cited from the literature; not machine-checked) | member | assumed | familywise(trial) |
| inspiratory_capacity_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited) | member | assumed | familywise(trial) |
| onset_of_action_sup: Null rejection probability is at most 1/40 whenever p_treatment - p_control <= 0. (declared by the author; not checked and not cited) | member | assumed | familywise(trial) |
| tdi_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -1. (declared by the author; not checked and not cited) | member | assumed | familywise(trial) |
| emsci_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -1/10. (declared by the author; not checked and not cited) | member | assumed | familywise(trial) |

## Outstanding obligations

None.

## Requested claims

- (unnamed) (familywise, verification requested): Probability of rejecting any true member null is at most 1/40 in the limit as each member's sample size or number of events grows, whenever any subset of the member nulls is true. No bound is claimed at the declared sample sizes.
- (unnamed) (familywise, verification requested): Probability of rejecting any true member null is at most 1/40 in the limit as each member's sample size or number of events grows, whenever any subset of the member nulls is true. No bound is claimed at the declared sample sizes.

## Justifications

## Contract for `trough_fev1_ni`

**Contract:** `tests.declared/declared_test`

**Conclusion:** trough_fev1_ni: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: trough_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: trough_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: trough_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: trough_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): trough_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: trough_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= -50. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.6.1

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `peak_fev1_ni`

**Contract:** `tests.declared/declared_test`

**Conclusion:** peak_fev1_ni: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: peak_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: peak_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: peak_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: peak_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): peak_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: peak_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= -50. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.6.2

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `peak_fev1_sup`

**Contract:** `tests.declared/declared_test`

**Conclusion:** peak_fev1_sup: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: peak_fev1_sup: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 500, n_treatment 500; null model: n_control 500, n_treatment 500
2. **supported-null**: peak_fev1_sup: the declared null (mean_treatment - mean_control <= 0) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: peak_fev1_sup: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: peak_fev1_sup: arm sizes (500, 500) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 500; n treatment: 500; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): peak_fev1_sup: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: peak_fev1_sup: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= 0. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.6.2

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `co_primary`

**Contract:** `multiplicity.graphical/graphical`

**Conclusion:** co_primary: its tests, shares and transitions form one graphical procedure.

### Why it passed

1. **same-model**: trough_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: trough_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: trough_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: trough_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): trough_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **same-model**: peak_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
7. **supported-null**: peak_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
8. **level-interior**: peak_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
9. **enough-data**: peak_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
10. **cited-contract** (from steps 6, 7, 8, 9): peak_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
11. **same-model**: peak_fev1_sup: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 500, n_treatment 500; null model: n_control 500, n_treatment 500
12. **supported-null**: peak_fev1_sup: the declared null (mean_treatment - mean_control <= 0) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
13. **level-interior**: peak_fev1_sup: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
14. **enough-data**: peak_fev1_sup: arm sizes (500, 500) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 500; n treatment: 500; min per arm: 1; min total: 2
15. **cited-contract** (from steps 11, 12, 13, 14): peak_fev1_sup: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
16. **distinct-members**: co_primary: the member analyses are distinct.
   - Rule: No analysis is listed twice.
   - Facts: members: trough_fev1_ni, peak_fev1_ni, peak_fev1_sup
17. **family-size**: co_primary: the family size 3 is supported.
   - Rule: The family has between 2 and 20 analyses.
   - Facts: count: 3
18. **full-level**: co_primary: every test uses the full level 1/40.
   - Rule: Every test in the sequence uses the sequence's level.
   - Facts: alpha: 1/40
19. **graph-weights**: co_primary: the starting shares ['1/2', '1/2', '0'] sum to 1.
   - Rule: There is one starting share for each test, each from 0 to 1, summing to at most 1.
   - Facts: weights: 1/2, 1/2, 0; total: 1
20. **graph-transitions**: co_primary: every row of transitions is a valid way to pass a level on.
   - Rule: Each test has one row of shares, from 0 to 1, passing nothing to itself and at most its whole level in total.
   - Facts: transitions: ['0', '1', '0'], ['0', '0', '1'], ['1', '0', '0']
21. **graphical-contract** (from steps 5, 10, 15, 16, 17, 18, 19, 20): co_primary: its tests, shares and transitions form one graphical procedure.
   - Rule: Every test satisfies its own contract, and the distinct-members, family-size, full-level, graph-weights and graph-transitions rules hold.
22. **fixed-sampling**: trough_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
23. **fixed-sampling**: peak_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
24. **fixed-sampling**: peak_fev1_sup: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Probability of rejecting any true member null is at most 1/40 in the limit as each member's sample size or number of events grows, whenever any subset of the member nulls is true. No bound is claimed at the declared sample sizes.

Cited from Graphical multiple testing procedure (`graphical`, version 1); not proved in Lean.

- Bretz, F., Maurer, W., Brannath, W. and Posch, M. (2009). A graphical approach to sequentially rejective multiple test procedures. Statistics in Medicine 28(4), 586-604.
- Burman, C.-F., Sonesson, C. and Guilbaud, O. (2009). A recycling framework for the construction of Bonferroni-based multiple tests. Statistics in Medicine 28(5), 739-761.

### Assumptions you must meet in the real study

- The tests, their starting shares of the level and the rules for passing a share on are fixed in advance, and a share is passed on only after a rejection. Each test controls its error at every level up to the overall level, not only at one.
- trough_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited)
- peak_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited)
- peak_fev1_sup: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= 0. (declared by the author; not checked and not cited)
- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is cited from the literature and holds only under the listed assumptions. It is not proved here or in Lean.

Independent check of this derivation: passed.

## Contract for `inspiratory_capacity_ni`

**Contract:** `tests.declared/declared_test`

**Conclusion:** inspiratory_capacity_ni: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: inspiratory_capacity_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: inspiratory_capacity_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: inspiratory_capacity_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: inspiratory_capacity_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): inspiratory_capacity_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: inspiratory_capacity_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= -50. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.7.2

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `onset_of_action_sup`

**Contract:** `tests.declared/declared_test`

**Conclusion:** onset_of_action_sup: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: onset_of_action_sup: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 500, n_treatment 500; null model: n_control 500, n_treatment 500
2. **supported-null**: onset_of_action_sup: the declared null (p_treatment - p_control <= 0) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: proportion_difference_at_most; supported: proportion_difference_at_most
3. **level-interior**: onset_of_action_sup: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: onset_of_action_sup: arm sizes (500, 500) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 500; n treatment: 500; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): onset_of_action_sup: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: onset_of_action_sup: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever p_treatment - p_control <= 0. No bound is claimed at the declared sample sizes.

Declared by the author as: Logistic regression, treatment coefficient. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.7.3

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `tdi_ni`

**Contract:** `tests.declared/declared_test`

**Conclusion:** tdi_ni: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: tdi_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: tdi_ni: the declared null (mean_treatment - mean_control <= -1) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: tdi_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: tdi_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): tdi_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: tdi_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= -1. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.7.4

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `emsci_ni`

**Contract:** `tests.declared/declared_test`

**Conclusion:** emsci_ni: the design, the null and the level fit this cited method.

### Why it passed

1. **same-model**: emsci_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: emsci_ni: the declared null (mean_treatment - mean_control <= -1/10) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: emsci_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: emsci_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): emsci_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **fixed-sampling**: emsci_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Null rejection probability is at most 1/40 in the limit as the sample sizes grow, whenever mean_treatment - mean_control <= -1/10. No bound is claimed at the declared sample sizes.

Declared by the author as: Mixed model for repeated measures, treatment contrast over 24 weeks. StatClaim has no contract or source for this test and checked nothing about its guarantee.

- Statistical analysis plan edition 2.0, section 4.2.7.5

### Assumptions you must meet in the real study

- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The guarantee below is the author's own statement about a test StatClaim has no contract or source for. Nothing about it is checked.

Independent check of this derivation: passed.

## Contract for `trial`

**Contract:** `multiplicity.fixed_sequence/fixed_sequence`

**Conclusion:** trial: its tests form one fixed sequence.

### Why it passed

1. **same-model**: trough_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
2. **supported-null**: trough_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
3. **level-interior**: trough_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
4. **enough-data**: trough_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
5. **cited-contract** (from steps 1, 2, 3, 4): trough_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
6. **same-model**: peak_fev1_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
7. **supported-null**: peak_fev1_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
8. **level-interior**: peak_fev1_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
9. **enough-data**: peak_fev1_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
10. **cited-contract** (from steps 6, 7, 8, 9): peak_fev1_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
11. **same-model**: peak_fev1_sup: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 500, n_treatment 500; null model: n_control 500, n_treatment 500
12. **supported-null**: peak_fev1_sup: the declared null (mean_treatment - mean_control <= 0) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
13. **level-interior**: peak_fev1_sup: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
14. **enough-data**: peak_fev1_sup: arm sizes (500, 500) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 500; n treatment: 500; min per arm: 1; min total: 2
15. **cited-contract** (from steps 11, 12, 13, 14): peak_fev1_sup: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
16. **distinct-members**: co_primary: the member analyses are distinct.
   - Rule: No analysis is listed twice.
   - Facts: members: trough_fev1_ni, peak_fev1_ni, peak_fev1_sup
17. **family-size**: co_primary: the family size 3 is supported.
   - Rule: The family has between 2 and 20 analyses.
   - Facts: count: 3
18. **full-level**: co_primary: every test uses the full level 1/40.
   - Rule: Every test in the sequence uses the sequence's level.
   - Facts: alpha: 1/40
19. **graph-weights**: co_primary: the starting shares ['1/2', '1/2', '0'] sum to 1.
   - Rule: There is one starting share for each test, each from 0 to 1, summing to at most 1.
   - Facts: weights: 1/2, 1/2, 0; total: 1
20. **graph-transitions**: co_primary: every row of transitions is a valid way to pass a level on.
   - Rule: Each test has one row of shares, from 0 to 1, passing nothing to itself and at most its whole level in total.
   - Facts: transitions: ['0', '1', '0'], ['0', '0', '1'], ['1', '0', '0']
21. **graphical-contract** (from steps 5, 10, 15, 16, 17, 18, 19, 20): co_primary: its tests, shares and transitions form one graphical procedure.
   - Rule: Every test satisfies its own contract, and the distinct-members, family-size, full-level, graph-weights and graph-transitions rules hold.
22. **same-model**: inspiratory_capacity_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
23. **supported-null**: inspiratory_capacity_ni: the declared null (mean_treatment - mean_control <= -50) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
24. **level-interior**: inspiratory_capacity_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
25. **enough-data**: inspiratory_capacity_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
26. **cited-contract** (from steps 22, 23, 24, 25): inspiratory_capacity_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
27. **same-model**: onset_of_action_sup: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 500, n_treatment 500; null model: n_control 500, n_treatment 500
28. **supported-null**: onset_of_action_sup: the declared null (p_treatment - p_control <= 0) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: proportion_difference_at_most; supported: proportion_difference_at_most
29. **level-interior**: onset_of_action_sup: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
30. **enough-data**: onset_of_action_sup: arm sizes (500, 500) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 500; n treatment: 500; min per arm: 1; min total: 2
31. **cited-contract** (from steps 27, 28, 29, 30): onset_of_action_sup: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
32. **same-model**: tdi_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
33. **supported-null**: tdi_ni: the declared null (mean_treatment - mean_control <= -1) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
34. **level-interior**: tdi_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
35. **enough-data**: tdi_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
36. **cited-contract** (from steps 32, 33, 34, 35): tdi_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
37. **same-model**: emsci_ni: the null and the design describe the same study model.
   - Rule: The design and the null refer to the same model.
   - Facts: design model: n_control 440, n_treatment 440; null model: n_control 440, n_treatment 440
38. **supported-null**: emsci_ni: the declared null (mean_treatment - mean_control <= -1/10) is supported by this analysis.
   - Rule: The null's form, its margin where the analysis fixes one, and its direction where the model declares which direction is better, are supported.
   - Facts: predicate: mean_difference_at_most; supported: mean_difference_at_most
39. **level-interior**: emsci_ni: the level 1/40 lies strictly between 0 and 1.
   - Rule: The level is strictly between 0 and 1.
   - Facts: alpha: 1/40
40. **enough-data**: emsci_ni: arm sizes (440, 440) meet the method's minimum of 1 per arm and 2 in total.
   - Rule: Each arm and the whole study are large enough for the method to estimate variance.
   - Facts: n control: 440; n treatment: 440; min per arm: 1; min total: 2
41. **cited-contract** (from steps 37, 38, 39, 40): emsci_ni: the design, the null and the level fit this cited method.
   - Rule: The same-model, supported-null, level-interior and enough-data rules hold.
42. **distinct-members**: trial: the member analyses are distinct.
   - Rule: No analysis is listed twice.
   - Facts: members: co_primary, inspiratory_capacity_ni, onset_of_action_sup, tdi_ni, emsci_ni
43. **family-size**: trial: the family size 5 is supported.
   - Rule: The family has between 2 and 20 analyses.
   - Facts: count: 5
44. **full-level**: trial: every test uses the full level 1/40.
   - Rule: Every test in the sequence uses the sequence's level.
   - Facts: alpha: 1/40
45. **fixed-sequence-contract** (from steps 21, 26, 31, 36, 41, 42, 43, 44): trial: its tests form one fixed sequence.
   - Rule: Every test satisfies its own contract, and the distinct-members, family-size and full-level rules hold.
46. **fixed-sampling**: trough_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
47. **fixed-sampling**: peak_fev1_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
48. **fixed-sampling**: peak_fev1_sup: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
49. **fixed-sampling**: inspiratory_capacity_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
50. **fixed-sampling**: onset_of_action_sup: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
51. **fixed-sampling**: tdi_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed
52. **fixed-sampling**: emsci_ni: sampling is fixed, as the fixed-sample error theorem requires.
   - Rule: The sample sizes are fixed before outcomes are observed.
   - Facts: stopping: fixed

### Guarantee, given the assumptions

Probability of rejecting any true member null is at most 1/40 in the limit as each member's sample size or number of events grows, whenever any subset of the member nulls is true. No bound is claimed at the declared sample sizes.

This follows from the members' own error bounds, which are assumed. Lean checks the combination when you verify the familywise claim.

### Assumptions you must meet in the real study

- The tests and their order are fixed in advance, and a test is carried out only if every earlier test in the order rejected.
- co_primary: Probability of rejecting any true member null is at most 1/40 whenever any subset of the member nulls is true. (cited from the literature; not machine-checked)
- inspiratory_capacity_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited)
- onset_of_action_sup: Null rejection probability is at most 1/40 whenever p_treatment - p_control <= 0. (declared by the author; not checked and not cited)
- tdi_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -1. (declared by the author; not checked and not cited)
- emsci_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -1/10. (declared by the author; not checked and not cited)
- The tests, their starting shares of the level and the rules for passing a share on are fixed in advance, and a share is passed on only after a rejection. Each test controls its error at every level up to the overall level, not only at one.
- trough_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited)
- peak_fev1_ni: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= -50. (declared by the author; not checked and not cited)
- peak_fev1_sup: Null rejection probability is at most 1/40 whenever mean_treatment - mean_control <= 0. (declared by the author; not checked and not cited)
- The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test.
- Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked.

### Unresolved obligations

None.

### Not established here

The familywise bound below follows from the members' own error bounds, which are assumed here. Lean checks the combination when you verify the familywise claim.

Independent check of this derivation: passed.
