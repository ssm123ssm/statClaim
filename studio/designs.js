// Every design the language supports, as a card the wizard can start from, and the .stat
// source each one builds. Pure functions: no DOM, so tests can build every combination.

// Exact numbers ------------------------------------------------------------------------
const gcd = (a, b) => b ? gcd(b, a % b) : Math.abs(a);
const reduce = (n, d) => { const g = gcd(n, d) || 1; return d / g < 0 ? [-n / g, -d / g] : [n / g, d / g]; };
// "1/20", "0.05" or "3" as [numerator, denominator], or null.
export function ratio(text) {
  const s = String(text).trim();
  let m = /^(-?\d+)\/(\d+)$/.exec(s);
  if (m && Number(m[2])) return reduce(Number(m[1]), Number(m[2]));
  m = /^(-?)(\d*)\.(\d+)$/.exec(s);
  if (m) { const d = 10 ** m[3].length; return reduce((m[1] ? -1 : 1) * (Number(m[2] || 0) * d + Number(m[3])), d); }
  return /^-?\d+$/.test(s) ? [Number(s), 1] : null;
}
const written = ([n, d]) => d === 1 ? String(n) : n + '/' + d;
// text × n / d, kept exact: times('1/20', 1, 2) is '1/40'.
export const times = (text, n, d = 1) => { const r = ratio(text); return r ? written(reduce(r[0] * n, r[1] * d)) : String(text); };
export function eval_(text) {
  const r = ratio(text);
  return r ? r[0] / r[1] : NaN;
}
export const fraction = text => /^\d+(\/\d+)?$|^\d*\.\d+$/.test(String(text).trim());
export const isShare = text => eval_(text) > 0 && eval_(text) < 1;
export const isWhole = text => /^\d+$/.test(String(text).trim()) && Number(text) > 0;
// Names in claims: a few plain words, as the language accepts them.
export const studyName = text => /^[A-Za-z][A-Za-z0-9 _'()-]{0,59}$/.test(String(text));
const quoted = text => JSON.stringify(String(text));
const finish = lines => lines.join('\n').replace(/\n{3,}/g, '\n\n').replace(/\n*$/, '\n');
const half = n => [Math.floor(Number(n) / 2), Number(n) - Math.floor(Number(n) / 2)];

// The catalogue ------------------------------------------------------------------------
// Five families keep the list short; search reaches every card by its words.
export const FAMILIES = [
  {id: 'trials', label: 'Trials', title: 'Randomised trials', detail: 'Treatment against control, assigned at random.', family: 'study', glyph: 'trial'},
  {id: 'several', label: 'Several', title: 'Several tests', detail: 'Several outcomes, or a look before the end.', family: 'family', glyph: 'several'},
  {id: 'single', label: 'One group', title: 'One group', detail: 'A single arm and its response rate.', family: 'planning', glyph: 'single'},
  {id: 'observed', label: 'Observed', title: 'Observational studies', detail: 'Exposure was observed, not assigned.', family: 'data', glyph: 'cohort'},
  {id: 'adjusted', label: 'Covariates', title: 'Covariates and surveys', detail: 'Cited regression, correlation and survey tests.', family: 'analysis', glyph: 'adjust'},
];

// A card starts a flow with some answers already given. evidence is what the guarantee
// rests on with those answers; cards whose evidence depends on later answers leave it out.
export const DESIGNS = [
  {id: 'two_arm', family: 'trials', flow: 'trial', label: 'Two-arm trial', detail: 'One outcome, treatment against control.', glyph: 'trial',
    words: 'rct randomised controlled superiority fisher t-test log-rank yes no binary measurement continuous survival time to event', preset: {}},
  {id: 'non_inferiority', family: 'trials', flow: 'trial', label: 'Non-inferiority', detail: 'No worse than control, within a margin.', glyph: 'margin',
    words: 'margin noninferiority not worse equivalence one-sided', preset: {question: 'margin'}},
  {id: 'randomisation', family: 'trials', flow: 'trial', label: 'Randomisation test', detail: 'Lean proves its level from the randomisation itself.', glyph: 'dice', evidence: 'proved',
    words: 'permutation rerandomisation sharp null exact any outcome distribution free', preset: {test: 'randomisation_test', outcome: 'continuous'}},
  {id: 'stratified', family: 'trials', flow: 'trial', label: 'Stratified or blocked', detail: 'Randomised within strata, or in blocks.', glyph: 'blocks', evidence: 'proved',
    words: 'strata stratum block permuted blocks stratified randomisation', preset: {test: 'randomisation_test', outcome: 'continuous', scheme: 'blocked'}},
  {id: 'cluster', family: 'trials', flow: 'trial', label: 'Cluster-randomised', detail: 'Whole clinics or schools are assigned.', glyph: 'cluster',
    words: 'clusters clinics schools villages practices group randomised cluster t-test', preset: {unit: 'clusters', outcome: 'continuous'}},
  {id: 'repeated', family: 'trials', flow: 'trial', label: 'Repeated visits', detail: 'The outcome measured at several visits.', glyph: 'visits', evidence: 'cited',
    words: 'longitudinal mmrm mixed model repeated measures visits follow-up', preset: {outcome: 'repeated'}},
  {id: 'declared', family: 'trials', flow: 'trial', label: 'Your own test', detail: 'Name a test StatClaim has no contract for.', glyph: 'pencil', evidence: 'declared',
    words: 'declared custom other method van elteren cmh vouch', preset: {test: 'declared_test', outcome: 'continuous'}},

  {id: 'outcomes', family: 'several', flow: 'several', label: 'Several outcomes', detail: 'Split the level between them: Bonferroni.', glyph: 'several',
    words: 'multiple endpoints multiplicity bonferroni familywise co-primary secondary', preset: {procedure: 'bonferroni'}},
  {id: 'sequence', family: 'several', flow: 'several', label: 'Fixed sequence', detail: 'Test in order, each at the full level.', glyph: 'sequence', evidence: 'conditional',
    words: 'hierarchical gatekeeping ordered fixed sequence familywise', preset: {procedure: 'fixed_sequence'}},
  {id: 'graphical', family: 'several', flow: 'several', label: 'Graphical procedure', detail: 'Pass the level on after a rejection.', glyph: 'graph', evidence: 'cited',
    words: 'graph recycling weights transitions bretz maurer familywise', preset: {procedure: 'graphical'}},
  {id: 'interim', family: 'several', flow: 'interim', label: 'Interim look', detail: 'Look early and stop at the first rejection.', glyph: 'looks', evidence: 'conditional',
    words: 'group sequential alpha spending stop early halfway interim analysis', preset: {}},

  {id: 'one_arm', family: 'single', flow: 'one_arm', label: 'Single-arm test', detail: 'Is the response rate above a benchmark?', glyph: 'single', evidence: 'proved',
    words: 'one sample binomial phase 2 response rate benchmark exact', preset: {aim: 'test'}},
  {id: 'rate_interval', family: 'single', flow: 'one_arm', label: 'Estimate a rate', detail: 'An exact interval for one response rate.', glyph: 'interval', evidence: 'proved',
    words: 'confidence interval clopper pearson proportion estimate', preset: {aim: 'estimate'}},
  {id: 'two_stage', family: 'single', flow: 'two_stage', label: 'Two-stage design', detail: 'Stop after stage one if few respond.', glyph: 'stages', evidence: 'proved',
    words: 'simon optimal minimax phase 2 interim futility two stage', preset: {rule: 'threshold'}},
  {id: 'bayesian', family: 'single', flow: 'two_stage', label: 'Bayesian two-stage', detail: 'Posterior thresholds, with the error checked.', glyph: 'prior', evidence: 'proved',
    words: 'bayes posterior beta prior probability two stage', preset: {rule: 'posterior', find: 'given'}},

  {id: 'cohort', family: 'observed', flow: 'observed', label: 'Cohort', detail: 'Followed forward to the outcome.', glyph: 'cohort', evidence: 'proved',
    words: 'prospective follow-up exposed unexposed risk ratio cumulative incidence', preset: {design: 'cohort'}},
  {id: 'case_control', family: 'observed', flow: 'observed', label: 'Case-control', detail: 'Asked back about exposure.', glyph: 'case_control', evidence: 'proved',
    words: 'retrospective cases controls odds ratio', preset: {design: 'case_control'}},
  {id: 'cross_sectional', family: 'observed', flow: 'observed', label: 'Cross-sectional', detail: 'Exposure and outcome measured at once.', glyph: 'cross_sectional', evidence: 'proved',
    words: 'survey prevalence snapshot prevalence ratio', preset: {design: 'cross_sectional'}},
  {id: 'matched_case_control', family: 'observed', flow: 'observed', label: 'Matched pairs', detail: 'Each case with one matched control.', glyph: 'matched_case_control', evidence: 'proved',
    words: 'matched case-control mcnemar pairs conditional odds ratio', preset: {design: 'matched_case_control'}},
  {id: 'prevalence_survey', family: 'observed', flow: 'observed', label: 'Prevalence survey', detail: 'How many for a margin of error.', glyph: 'cross_sectional',
    words: 'prevalence precision margin of error confidence interval survey estimate sample size assurance',
    preset: {design: 'cross_sectional', add: 'precision', precisionMeasure: 'prevalence'}},
  {id: 'person_time', family: 'observed', flow: 'observed', label: 'Person-time cohort', detail: 'Events over person-years: incidence rates.', glyph: 'person_time', evidence: 'proved',
    words: 'incidence rate ratio person-years events occupational cohort poisson', preset: {design: 'person_time'}},

  {id: 'logistic_trial', family: 'adjusted', flow: 'trial', label: 'Trial with covariates', detail: 'Logistic regression on a yes-or-no outcome.', glyph: 'adjust', evidence: 'cited',
    words: 'adjusted covariates logistic regression baseline randomised', preset: {outcome: 'binary', test: 'logistic_regression'}},
  {id: 'regression', family: 'adjusted', flow: 'observed', label: 'Regression with covariates', detail: 'An observational test, adjusted for confounders.', glyph: 'adjust', evidence: 'cited',
    words: 'confounders adjusted logistic poisson linear regression covariates', preset: {design: 'cohort', test: 'logistic_association'}},
  {id: 'correlation', family: 'adjusted', flow: 'observed', label: 'Correlation', detail: 'Two measurements in one sample.', glyph: 'correlation', evidence: 'cited',
    words: 'pearson spearman rank correlation continuous', preset: {design: 'cross_sectional', outcomeScale: 'continuous', exposureScale: 'continuous', test: 'pearson_correlation'}},
  {id: 'survey', family: 'adjusted', flow: 'observed', label: 'Complex survey', detail: 'Strata, clusters or sampling weights.', glyph: 'survey', evidence: 'cited',
    words: 'weighted design-based rao-scott survey logistic national stratified cluster sample', preset: {design: 'cross_sectional', survey: 'weighted', test: 'survey_logistic'}},
];
export const designById = id => DESIGNS.find(d => d.id === id);
// What the guarantee rests on, in the wizard's words.
export const EVIDENCE = {
  proved: {label: 'Proved in Lean', sentence: 'Its Type I error bound is proved in Lean.'},
  cited: {label: 'Cited', sentence: 'Its Type I error bound is cited from the literature, not proved here.'},
  conditional: {label: 'Combination checked', sentence: 'Lean checks how the level is shared; each test\'s own bound is assumed.'},
  declared: {label: 'Declared', sentence: 'You vouch for this test: only its fit to the design is checked.'},
};

// Two-arm trials -----------------------------------------------------------------------
export const OUTCOMES = {
  binary: {label: 'Yes or no', example: 'such as response to treatment', model: 'two_arm_binomial', module: 'models.two_arm_binomial', piece: 'binary_outcome'},
  continuous: {label: 'A measurement', example: 'such as blood pressure or a symptom score', model: 'two_arm_continuous', module: 'models.two_arm_continuous', piece: 'continuous_outcome'},
  repeated: {label: 'Measured at each visit', example: 'the same measurement, visit after visit', model: null, module: 'models.two_arm_continuous', piece: 'continuous_outcome'},
  survival: {label: 'Time to an event', example: 'such as time to relapse, possibly censored', model: 'two_arm_survival', module: 'models.two_arm_survival', piece: 'survival_outcome'},
};
export const QUESTIONS = {
  differ: {label: 'Do the arms differ?', detail: 'Two-sided: either direction counts.'},
  better: {label: 'Is the treatment better?', detail: 'One-sided: superiority.'},
  margin: {label: 'Is it no worse than control?', detail: 'One-sided: non-inferiority, within a margin.'},
};
// Which questions each outcome can answer today, and why not when it cannot.
export function available(outcome, better) {
  if (outcome === 'survival') return {differ: true, why: 'For time to an event, StatClaim has two-sided tests only.'};
  if (outcome === 'binary' && better === 'lower') {
    return {differ: true, why: 'For a yes-or-no outcome where fewer is better, StatClaim has only two-sided tests today.'};
  }
  return {differ: true, better: true, margin: true};
}
const binaryOnes = s => s.outcome === 'binary' && s.unit !== 'clusters';
// The tests a trial can use, strongest and most usual first. call gives the constructor
// for the question; fits says whether it can answer it for this outcome and assignment.
export const TRIAL_TESTS = {
  fisher: {label: "Fisher's exact test", module: 'tests.fisher', evidence: 'proved',
    call: s => s.question === 'differ' ? 'fisher' : 'fisher_one_sided', fits: s => binaryOnes(s) && s.question !== 'margin'},
  difference_test: {label: 'Exact difference test', detail: 'Up to 120 per arm.', module: 'tests.difference', evidence: 'proved',
    call: () => 'difference_test', fits: s => binaryOnes(s) && s.question !== 'differ'},
  t_test: {label: 'Pooled-variance t-test', module: 'tests.t', evidence: 'cited',
    call: s => s.question === 'differ' ? 't_test' : 't_test_one_sided', fits: s => s.outcome === 'continuous' && s.unit !== 'clusters'},
  welch_test: {label: 'Welch t-test', detail: 'Unequal variances allowed.', module: 'tests.t', evidence: 'cited',
    call: s => s.question === 'differ' ? 'welch_test' : 'welch_test_one_sided', fits: s => s.outcome === 'continuous' && s.unit !== 'clusters'},
  mmrm_test: {label: 'Mixed model for repeated measures', module: 'tests.mixed_model', evidence: 'cited',
    call: s => s.question === 'differ' ? 'mmrm_test' : 'mmrm_test_one_sided', fits: s => s.outcome === 'repeated' && s.unit !== 'clusters'},
  log_rank: {label: 'Log-rank test', module: 'tests.survival', evidence: 'cited',
    call: () => 'log_rank', fits: s => s.outcome === 'survival' && s.unit !== 'clusters'},
  cluster_t_test: {label: 'Cluster-level t-test', detail: 'One summary per cluster.', module: 'tests.cluster', evidence: 'cited',
    call: s => s.outcome === 'binary' ? 'cluster_proportion_t_test' : 'cluster_t_test',
    fits: s => s.unit === 'clusters' && s.question === 'differ' && (s.outcome === 'binary' || s.outcome === 'continuous')},
  randomisation_test: {label: 'Randomisation test', detail: 'From how you randomised; no distribution assumed.', module: 'tests.randomisation', evidence: 'proved',
    call: () => 'randomisation_test', fits: s => s.question === 'differ'},
  logistic_regression: {label: 'Logistic regression', detail: 'Adjusts for baseline covariates.', module: 'tests.logistic', evidence: 'cited',
    call: s => s.question === 'differ' ? 'logistic_regression' : 'logistic_regression_one_sided', fits: s => binaryOnes(s) && s.question !== 'margin'},
  declared_test: {label: 'Your own test', detail: 'Name it and vouch for it.', module: 'tests.declared', evidence: 'declared',
    call: () => 'declared_test', fits: () => true},
};
export const trialTests = state => Object.keys(TRIAL_TESTS).filter(id => TRIAL_TESTS[id].fits(withTrialDefaults(state)));
const withTrialDefaults = s => ({outcome: 'binary', question: 'differ', unit: 'participants', ...s});
export const trialTest = state => trialTests(state).includes(state.test) ? state.test : trialTests(state)[0];

// What a run can add to a trial: the sample size, or the analysis of results.
export function trialExtras(state) {
  const s = withTrialDefaults(state);
  const test = trialTest(s);
  const plan = {fisher: 'exact', difference_test: 'exact', logistic_regression: 'formula', t_test: 'simulated', welch_test: 'simulated',
    mmrm_test: 'formula', log_rank: 'survival', cluster_t_test: 'clusters'}[test];
  return {plan, data: s.outcome === 'binary' && s.unit !== 'clusters'};
}

// Whether an expected difference lies outside the null the question tests, so power can be planned at it.
export function plannable({question = 'differ', better = 'higher', margin = '1/10', effect = '5'}) {
  const value = eval_(effect);
  if (!Number.isFinite(value)) return 'The expected difference must be a number, such as 5, -2.5 or 1/2.';
  const lower = better === 'lower';
  if (question === 'differ') return value !== 0 ? '' : 'The expected difference cannot be 0: there would be nothing to detect.';
  if (question === 'better') return (lower ? value < 0 : value > 0) ? '' : 'The expected difference must favour the treatment: ' + (lower ? 'below' : 'above') + ' 0.';
  const bound = eval_(margin);
  return (lower ? value < bound : value > -bound) ? '' : 'The expected difference must be ' + (lower ? 'below ' : 'above -') + margin + ', inside the margin.';
}
// The same for the response rates a yes-or-no trial is planned at.
export function ratesPlannable({question = 'differ', margin = '1/10', pControl = '3/10', pTreatment = '1/2'}) {
  if (!isShare(pControl) || !isShare(pTreatment)) return 'Each response rate must lie between 0 and 1, such as 3/10.';
  const gap = eval_(pTreatment) - eval_(pControl);
  if (question === 'differ') return gap !== 0 ? '' : 'The two rates cannot be equal: there would be nothing to detect.';
  if (question === 'better') return gap > 0 ? '' : 'The treatment rate must be above the control rate.';
  return gap > -eval_(margin) ? '' : 'The treatment rate must be within the margin of the control rate.';
}

// The .stat source for a trial, and what its guarantee rests on.
export function studySource(state) {
  const {name = 'study', outcome = 'binary', control = 50, treatment = 50, better = 'higher', margin = '1/10', alpha = '1/20',
    unit = 'participants', clustersControl = 12, clustersTreatment = 12, visits = 3, scheme = 'complete', blockSize = 4, draws = 'every',
    method = 'Stratified Cochran-Mantel-Haenszel test', reference = '', effect = '5', sd = '10', seed = 2026, icc = '1/20',
    pControl = '3/10', pTreatment = '1/2', hazard = '7/10', median = '12', accrual = '24', followUp = '12',
    controlSuccesses = 12, treatmentSuccesses = 24} = state;
  const allowed = available(outcome, better);
  const question = allowed[state.question] ? state.question : 'differ';
  const s = {...state, outcome, question, unit};
  const test = trialTest(s);
  const info = TRIAL_TESTS[test];
  const call = info.call(s);
  const kind = OUTCOMES[outcome];
  const lower = better === 'lower';
  const directional = question !== 'differ';
  // The older `plan: true` meant simulating a measured outcome; `add` says it for every test.
  const add = state.add || (state.plan ? 'plan' : 'none');
  const extras = trialExtras(s);
  const planning = add === 'plan' && extras.plan ? extras.plan : null;
  const analysing = add === 'data' && extras.data;

  let null_;
  if (test === 'randomisation_test') null_ = 'no_effect(model=study)';
  else if (outcome === 'binary') {
    null_ = question === 'differ' ? 'equal_proportions(model=study)' :
      'proportion_difference_at_most(model=study, value=' + (question === 'better' ? '0' : '-' + margin) + ')';
  } else if (outcome === 'survival') null_ = 'equal_survival(model=study)';
  else if (question === 'differ') null_ = 'equal_means(model=study)';
  else {
    const value = question === 'better' ? '0' : (lower ? margin : '-' + margin);
    null_ = (lower ? 'mean_difference_at_least' : 'mean_difference_at_most') + '(model=study, value=' + value + ')';
  }
  const words = {differ: 'do the arms differ?', better: 'is the treatment better?',
    margin: 'is the treatment no worse than control by more than ' + margin + '?'}[question];

  const uses = [kind.module, 'sampling', info.module];
  // Re-estimating a t-test's size at an interim look, from the blinded SD.
  const reestimate = planning === 'simulated' && test === 't_test' && state.reestimate === 'blinded' &&
    Number(control) === Number(treatment);
  if (reestimate) uses.push('designs.adaptive');
  if (planning) uses.push('planning');
  if (analysing) uses.push('estimation');
  const lines = ['# ' + name + ': ' + words, ...uses.map(m => 'use ' + m), ''];
  const direction = directional || (outcome !== 'binary' && lower) ? 'better="' + better + '"' : '';
  // Clusters, visits and declared randomisation need the pieces: an assignment and an outcome.
  const pieces = outcome === 'repeated' || unit === 'clusters' || test === 'randomisation_test';
  if (!pieces) {
    lines.push('let study = ' + kind.model + '(n_control=' + control + ', n_treatment=' + treatment + (direction ? ', ' + direction : '') + ')');
  } else {
    const clusters = unit === 'clusters';
    const args = clusters ?
      ['clusters_control=' + clustersControl, 'clusters_treatment=' + clustersTreatment, 'n_control=' + control, 'n_treatment=' + treatment] :
      ['n_control=' + control, 'n_treatment=' + treatment];
    if (test === 'randomisation_test') {
      args.push('randomisation="' + scheme + '"');
      if (scheme === 'stratified') {
        const [c1, c2] = half(clusters ? clustersControl : control);
        const [t1, t2] = half(clusters ? clustersTreatment : treatment);
        args.push('strata=[stratum(control=' + c1 + ', treatment=' + t1 + '), stratum(control=' + c2 + ', treatment=' + t2 + ')]');
      }
      if (scheme === 'blocked') args.push('block_size=' + blockSize);
    }
    const arms = clusters ? 'clinics' : 'arms';
    lines.push('let ' + arms + ' = ' + (clusters ? 'cluster_assignment' : 'assignment') + '(' + args.join(', ') + ')');
    const piece = [direction, outcome === 'repeated' ? 'measurements=' + visits : ''].filter(Boolean).join(', ');
    lines.push('let study = two_arm(assignment=' + arms + ', outcome=' + kind.piece + '(' + piece + '))');
  }
  lines.push('let design = fixed(model=study)', 'let null = ' + null_);
  const extra = test === 'randomisation_test' && draws === 'draws' ? ', draws=9999' :
    test === 'declared_test' ? ', method=' + quoted(method) + (String(reference).trim() ? ', reference=' + quoted(reference) : '') : '';
  lines.push('let analysis = ' + call + '(design=design, null=null, alpha=' + alpha + extra + ')');
  lines.push('let checked = verify(typeI(analysis))', '');

  const notes = [];
  if (reestimate) {
    const interim = Math.max(2, Math.min(Number(control) - 1, Number(state.interimN ?? Math.floor(Number(control) / 2))));
    const largest = Math.max(Number(control), Number(state.maxN ?? 3 * Number(control)));
    const sds = [times(sd, 3, 5), sd, times(sd, 7, 5)];
    lines.push('# After ' + interim + ' per arm, re-estimate the size from the SD of everyone pooled, without unblinding:',
      '# between ' + control + ' and ' + largest + ' per arm, for 80% power at a difference of ' + effect + '.',
      'let trial = blinded_reestimation(analysis=analysis, interim_per_arm=' + interim + ', difference=' + effect + ', power=4/5, max_per_arm=' + largest + ')',
      '# Its Type I error is not proved: it is judged at these SDs, up to 1.5 times alpha.',
      'let nulls = null_scenarios(at=[' + sds.map(value => 'mean_difference(value=0, sd=' + value + ')').join(', ') + '])',
      'let target = power_target(at=mean_difference(value=' + effect + ', sd=' + sd + '), minimum=4/5, maximum_typeI=' + times(alpha, 3, 2) + ', nulls=nulls)',
      'let check = simulate(meets(analysis=trial, target=target), seed=' + seed + ')',
      'let expected_total = check.calculation.expected_sample_size', '');
    notes.push('The re-estimated design is simulated: its power and Type I error are estimates, judged at the listed SDs only.');
  } else if (planning === 'simulated') {
    // Another scenario: the treatment arm's own SD, or a skewed outcome.
    const sdT = String(state.sdTreatment ?? '').trim();
    const skew = String(state.skew ?? '0').trim();
    const unequal = sdT !== '' && eval_(sdT) !== eval_(sd);
    const skewed = skew !== '' && eval_(skew) !== 0;
    const judged = unequal || skewed;
    const scenario = (unequal ? ', sd_treatment=' + sdT : '') + (skewed ? ', skewness=' + skew : '');
    lines.push('# The difference you expect, treatment minus control, and the SD of one participant\'s outcome' +
      (unequal ? ' in control, then in treatment' : '') + (skewed ? '; the outcome\'s skewness' : '') + '.',
      'let expected = mean_difference(value=' + effect + ', sd=' + sd + scenario + ')');
    if (judged) lines.push('# Here the test\'s level is not assured, so its simulated Type I is judged: at most 1.5 times alpha.');
    lines.push('let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + (judged ? times(alpha, 3, 2) : alpha) + ')',
      '# The smallest size per arm with at least 80% power, by simulating the test.',
      'let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=' + (skewed ? 200 : 1000) + ')');
    if (skewed) lines.push('# A skewed outcome is drawn participant by participant: 2,000 runs keep the search quick.');
    lines.push('let sizing = simulate(smallest_sample_size(candidates=sizes, target=target), seed=' + seed + (skewed ? ', runs=2000' : '') + ')',
      'let per_arm = sizing.calculation.n_control', '');
    notes.push('The sample size is estimated by simulation: an estimate, not a proof.');
    if (judged) notes.push('Type I is judged on the simulation, since this scenario leaves the test\'s theory.');
  } else if (planning === 'formula') {
    const point = outcome === 'binary' ? 'binomial_rates(p_control=' + pControl + ', p_treatment=' + pTreatment + ')' :
      'mean_difference(value=' + effect + ', sd=' + sd + ')';
    lines.push('# The smallest size per arm with at least 80% power, by the cited power formula.',
      'let expected = ' + point,
      'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ')',
      'let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=5000)',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let per_arm = sizing.calculation.n_control', '');
    notes.push(test === 'logistic_regression' ? 'The sample size is summed exactly over both arms\' counts for the Wald test; the test\'s level is cited.' :
      'The sample size comes from an approximate power formula, not a bound.');
  } else if (planning === 'exact') {
    const sufficient = test === 'difference_test';
    lines.push('# The response rates you expect, and the ' + (sufficient ? 'first size' : 'smallest size') + ' per arm with 80% power: exact.',
      'let expected = binomial_rates(p_control=' + pControl + ', p_treatment=' + pTreatment + ')',
      'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ')',
      'let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=' + (sufficient ? 120 : 500) + ')',
      'let sizing = calculate(' + (sufficient ? 'sample_size' : 'smallest_sample_size') + '(candidates=sizes, target=target))',
      'let per_arm = sizing.calculation.n_control', '');
    notes.push('The sample size comes from exact power, calculated; verify the sizing to have Lean check it.');
  } else if (planning === 'clusters') {
    // Clusters of unequal sizes are simulated; equal ones take the noncentral t.
    const cv = String(state.cv ?? '0').trim();
    const varied = cv !== '' && eval_(cv) > 0;
    const icc_ = ', icc=' + icc + (varied ? ', cluster_size_cv=' + cv : '');
    const point = outcome === 'binary' ? 'binomial_rates(p_control=' + pControl + ', p_treatment=' + pTreatment + icc_ + ')' :
      'mean_difference(value=' + effect + ', sd=' + sd + icc_ + ')';
    const size = Math.max(1, Math.round(Number(control) / Number(clustersControl)));
    const run = claim => varied ? 'simulate(' + claim + ', seed=' + seed + ')' : 'calculate(' + claim + ')';
    lines.push('# What you expect, and the intracluster correlation: how alike participants in one cluster are.',
      'let expected = ' + point,
      'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ')',
      'let power = ' + run('meets(analysis=analysis, target=target)'),
      '# The fewest clusters per arm with at least 80% power, each of ' + size + ' participants' + (varied ? ' on average.' : '.'),
      'let sizes = cluster_counts(analysis=analysis, cluster_size=' + size + ', min_per_arm=4, max_per_arm=' + (varied ? 200 : 1000) + ')',
      'let sizing = ' + run('smallest_sample_size(candidates=sizes, target=target)'),
      'let clusters_per_arm = sizing.calculation.clusters_control', '');
    notes.push(varied ? 'Clusters of unequal sizes are simulated: the number of clusters is an estimate, not a proof.' :
      'The number of clusters comes from the noncentral t at the planning values, not a bound.');
  } else if (planning === 'survival') {
    lines.push('# The hazard ratio you expect, the control median, and how long patients enter and are followed.',
      'let expected = exponential_survival(hazard_ratio=' + hazard + ', control_median=' + median + ', accrual=' + accrual + ', follow_up=' + followUp + ')',
      'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ')',
      '# The smallest size per arm with at least 80% power, at the events each size expects.',
      'let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=20000)',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let per_arm = sizing.calculation.n_control',
      'let events = sizing.calculation.expected_events', '');
    notes.push('The sample size comes from an approximate formula at the expected events, not a bound.');
    // A treatment that acts late: the formula cannot say, so the declared trial is simulated.
    const delay = String(state.delay ?? '0').trim();
    const total = Number(control) + Number(treatment);
    if (delay !== '' && eval_(delay) > 0 && total <= 60000) {
      // Every patient is drawn: fewer runs keep a large trial within the budget.
      const runs = Math.min(10000, Math.max(1000, Math.floor(60000000 / total / 1000) * 1000));
      lines.push('# If the treatment acts only from ' + delay + ' after entry: the declared trial, by simulation.',
        'let late = exponential_survival(hazard_ratio=' + hazard + ', control_median=' + median + ', accrual=' + accrual + ', follow_up=' + followUp + ', effect_delay=' + delay + ')',
        'let delayed = power_target(at=late, minimum=4/5, maximum_typeI=' + alpha + ')',
        'let delayed_power = simulate(meets(analysis=analysis, target=delayed), seed=' + seed + (runs < 10000 ? ', runs=' + runs : '') + ')', '');
      notes.push('Power with the delay is simulated: an estimate, not a proof.');
    }
  }
  if (analysing) {
    const exact = ['fisher', 'difference_test'].includes(test);
    lines.push('# The results: responders in each arm.');
    if (exact) {
      lines.push('let data = observe(analysis=analysis, control_successes=' + controlSuccesses + ', treatment_successes=' + treatmentSuccesses + ')',
        'let outcome_test = verify(result(data))');
    }
    lines.push('let interval = verify(difference_interval(model=study, control_successes=' + controlSuccesses +
      ', treatment_successes=' + treatmentSuccesses + ', level=19/20))', '');
  }
  return {source: finish(lines), test: call, evidence: info.evidence, question, notes};
}

// Several tests --------------------------------------------------------------------------
export const PROCEDURES = {
  bonferroni: {label: 'Bonferroni', detail: 'Each outcome gets an equal share of the level.', module: 'multiplicity.bonferroni', glyph: 'several'},
  fixed_sequence: {label: 'Fixed sequence', detail: 'In order, each at the full level, while they reject.', module: 'multiplicity.fixed_sequence', glyph: 'sequence'},
  graphical: {label: 'Graphical', detail: 'Equal shares, passed on after a rejection.', module: 'multiplicity.graphical', glyph: 'graph'},
};
// A binding name for an outcome's words, such as "symptom score" → symptom_score.
export function slug(text, taken = new Set()) {
  let base = String(text).toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_+|_+$/g, '') || 'outcome';
  if (!/^[a-z]/.test(base)) base = 'outcome_' + base;
  if (['study', 'design', 'null', 'family', 'checked', 'arms', 'verify', 'calculate', 'simulate'].includes(base)) base += '_outcome';
  let name = base;
  for (let i = 2; taken.has(name); i++) name = base + '_' + i;
  taken.add(name);
  return name;
}
export function severalSource({name = 'study', procedure = 'bonferroni', control = 100, treatment = 100, alpha = '1/20',
  endpoints = [{name: 'response', kind: 'binary'}, {name: 'remission', kind: 'binary'}], severalAdd = 'none', rejecting = 'any',
  correlation = '1/2', pControl = '3/10', pTreatment = '1/2', effect = '5', sd = '10', seed = 2026}) {
  const k = endpoints.length;
  const info = PROCEDURES[procedure];
  const binary = endpoints.every(e => e.kind === 'binary');
  const kinds = new Set(endpoints.map(e => e.kind));
  const level = procedure === 'bonferroni' ? times(alpha, 1, k) : alpha;
  const power = severalAdd === 'power';
  const uses = [...(kinds.has('binary') ? ['models.two_arm_binomial'] : []), ...(kinds.has('continuous') ? ['models.two_arm_continuous'] : []),
    'sampling', ...(kinds.has('binary') ? ['tests.fisher'] : []), ...(kinds.has('continuous') ? ['tests.t'] : []), info.module,
    ...(power ? ['planning'] : [])];
  const lines = ['# ' + name + ': ' + k + ' outcomes on the same participants, ' + info.label.toLowerCase() + '.', ...uses.map(m => 'use ' + m), '',
    'let arms = assignment(n_control=' + control + ', n_treatment=' + treatment + ')'];
  const taken = new Set();
  const tests = endpoints.map(e => {
    const model = slug(e.name, taken);
    const test = slug(model + '_test', taken);
    const binaryOne = e.kind === 'binary';
    lines.push('let ' + model + ' = two_arm(assignment=arms, outcome=' + (binaryOne ? 'binary' : 'continuous') + '_outcome(name=' + quoted(e.name) + '))');
    lines.push('let ' + test + ' = ' + (binaryOne ? 'fisher' : 't_test') + '(design=fixed(model=' + model + '), null=' +
      (binaryOne ? 'equal_proportions' : 'equal_means') + '(model=' + model + '), alpha=' + level + ')');
    return test;
  });
  const list = '[' + tests.join(', ') + ']';
  if (procedure === 'bonferroni') {
    lines.push('let family = bonferroni(analyses=' + list + ', alpha=' + alpha + (binary ? ', joint_law="binomial_marginals"' : '') + ')');
  } else if (procedure === 'fixed_sequence') {
    lines.push('let family = fixed_sequence(analyses=' + list + ', alpha=' + alpha + ')');
  } else {
    const share = times('1', 1, k);
    const pass = times('1', 1, k - 1);
    const rows = endpoints.map((_, i) => '[' + endpoints.map((__, j) => i === j ? '0' : pass).join(', ') + ']');
    lines.push('let family = graphical(analyses=' + list + ', weights=[' + endpoints.map(() => share).join(', ') + '], transitions=[' + rows.join(', ') + '], alpha=' + alpha + ')');
  }
  lines.push('let checked = verify(familywise(family))', '');
  const evidence = procedure === 'graphical' ? 'cited' : procedure === 'bonferroni' && binary ? 'proved' : 'conditional';
  const notes = procedure === 'bonferroni' && binary ? ['A family of two-sided Fisher tests is proved outright.'] : [];
  // The family's power: each endpoint at its planning point, simulated together.
  if (power) {
    const points = endpoints.map(e => e.kind === 'binary' ? 'binomial_rates(p_control=' + pControl + ', p_treatment=' + pTreatment + ')' :
      'mean_difference(value=' + effect + ', sd=' + sd + ')');
    lines.push('# What you expect on each outcome, in order, and how strongly they move together in a participant.',
      'let expected = endpoint_points(at=[' + points.join(', ') + '], correlation=' + correlation + ')',
      '# Power to reject ' + (rejecting === 'all' ? 'every outcome' : 'at least one outcome') + ', simulated with the family\'s own procedure.',
      'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ', rejecting=' + quoted(rejecting) + ')',
      'let power = simulate(meets(analysis=family, target=target), seed=' + seed + ')', '');
    notes.push('The family\'s power is simulated: an estimate, not a proof.');
  }
  return {source: finish(lines), test: procedure, evidence, notes};
}

// An interim look: one test at two looks, the level spent across them.
export const SPENDING = {
  little: {label: 'Little early', detail: 'A tenth of the level at the look, the rest at the end.'},
  even: {label: 'Evenly', detail: 'Half the level at each.'},
};
const LOOK_TESTS = {binary: ['tests.fisher', 'fisher', 'equal_proportions'], continuous: ['tests.t', 't_test', 'equal_means'], survival: ['tests.survival', 'log_rank', 'equal_survival']};
export function interimSource({name = 'study', outcome = 'binary', control = 100, treatment = 100, interimControl = 50, interimTreatment = 50,
  spending = 'little', alpha = '1/20', interimAdd = 'none', effect = '5', sd = '10', seed = 2026, pControl = '3/10', pTreatment = '1/2'}) {
  const kind = OUTCOMES[outcome] || OUTCOMES.binary;
  const [module, test, nul] = LOOK_TESTS[outcome] || LOOK_TESTS.binary;
  const [early, late] = spending === 'even' ? [times(alpha, 1, 2), times(alpha, 1, 2)] : [times(alpha, 1, 10), times(alpha, 9, 10)];
  const lines = ['# ' + name + ': one test at an interim look and at the end, stopping at the first rejection.',
    'use ' + kind.module, 'use sampling', 'use ' + module, 'use designs.group_sequential', '',
    'let halfway = ' + kind.model + '(n_control=' + interimControl + ', n_treatment=' + interimTreatment + ')',
    'let complete = ' + kind.model + '(n_control=' + control + ', n_treatment=' + treatment + ')',
    'let interim = ' + test + '(design=fixed(model=halfway), null=' + nul + '(model=halfway), alpha=' + early + ')',
    'let final = ' + test + '(design=fixed(model=complete), null=' + nul + '(model=complete), alpha=' + late + ')',
    'let trial = alpha_spending(looks=[interim, final], alpha=' + alpha + ')',
    'let checked = verify(typeI(trial))', ''];
  const notes = ['The split is conservative: it ignores the correlation between looks.'];
  // Fisher's test at looks: power summed exactly over every path of counts.
  if (outcome === 'binary' && interimAdd === 'power') {
    lines.splice(4, 0, 'use planning');
    lines.push('# The response rates you expect: power, stopping at each look and the expected size, summed exactly.',
      'let target = power_target(at=binomial_rates(p_control=' + pControl + ', p_treatment=' + pTreatment + '), minimum=4/5, maximum_typeI=' + alpha + ')',
      'let power = calculate(meets(analysis=trial, target=target))',
      'let expected_total = power.calculation.expected_sample_size', '');
    notes.push('Power is summed exactly over every path of counts: a calculation, not a proof.');
  }
  // The t-tests' power is simulated look by look: power, stopping and the expected size.
  if (outcome === 'continuous' && interimAdd === 'power') {
    lines.splice(4, 0, 'use planning');
    lines.push('# The difference you expect and the SD: power, stopping at each look and the expected size, simulated.',
      'let target = power_target(at=mean_difference(value=' + effect + ', sd=' + sd + '), minimum=4/5, maximum_typeI=' + alpha + ')',
      'let power = simulate(meets(analysis=trial, target=target), seed=' + seed + ')',
      'let expected_total = power.calculation.expected_sample_size', '');
    notes.push('Power and the expected size are simulated: estimates, not proofs.');
  }
  return {source: finish(lines), test: 'alpha_spending', evidence: 'conditional', notes};
}

// One group ------------------------------------------------------------------------------
export const AIMS = {
  test: {label: 'Is it above a benchmark?', detail: 'A one-sided exact test of the response rate.', glyph: 'better'},
  estimate: {label: 'How large is it?', detail: 'An exact confidence interval.', glyph: 'interval'},
};
export function oneArmSource(state) {
  const {name = 'study', aim = 'test', n = 30, nullRate = '1/5', target = '2/5', alpha = '1/20', add = 'none', count = 12, level = '19/20'} = state;
  if (aim === 'estimate') {
    const precise = add === 'precision';
    const lines = ['# ' + name + ': how large is the response rate?', 'use tests.binomial', ...(precise ? ['use planning'] : []), '',
      'let study = one_arm_binomial(n=' + n + ')',
      'let interval = verify(confidence_interval(model=study, count=' + count + ', level=' + level + '))', ''];
    if (precise) {
      lines.push('# How many for the margin of error you want, at the rate you expect.',
        'let estimate = planned_interval(model=study, measure="response_rate")',
        ...precisionLines({...state, base: state.base ?? target}, 'response_rate(value=' + (state.base ?? target) + ')', 'interval_sizes(interval=estimate, min_size=5, max_size=100000)', 'total_sample_size'), '');
    }
    const notes = ['The interval is exact (Clopper-Pearson), with checked coverage.'];
    if (precise) notes.push('The size comes from the exact interval\'s precision, calculated; Lean does not check precision.');
    return {source: finish(lines), test: 'confidence_interval', evidence: 'proved', notes};
  }
  const lines = ['# ' + name + ': is the response rate above ' + nullRate + '?', 'use tests.binomial', 'use planning', '',
    'let study = one_arm_binomial(n=' + n + ')',
    'let analysis = binomial_test(model=study, null_rate=' + nullRate + ', alpha=' + alpha + ')',
    '# The rate you hope for: Type I error and 80% power there are checked together.',
    'let target = power_target(at=response_rate(value=' + target + '), minimum=4/5, maximum_typeI=' + alpha + ')',
    'let checked = verify(meets(analysis=analysis, target=target))', ''];
  if (add === 'plan') {
    lines.push('let sizes = sample_sizes(analysis=analysis, min_n=5, max_n=300)',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))', 'let n_needed = sizing.calculation.n', '');
  }
  if (add === 'data') {
    lines.push('let data = responses(analysis=analysis, count=' + count + ')', 'let outcome_test = verify(binomial_result(data))',
      'let interval = verify(confidence_interval(model=study, count=' + count + ', level=19/20))', '');
  }
  return {source: finish(lines), test: 'binomial_test', evidence: 'proved',
    notes: add === 'plan' ? ['The sample size comes from exact power, calculated.'] : []};
}

// Precision: the margin of error a planned interval should have, absolute or relative, and
// an optional assurance, the chance that the interval comes out that narrow.
export const MARGIN_KINDS = {absolute: {label: 'Absolute', detail: 'Half the width'}, relative: {label: 'Relative', detail: 'Of the planning value'}};
const RATIO_MEASURES = new Set(['risk_ratio', 'prevalence_ratio', 'odds_ratio', 'conditional_odds_ratio', 'rate_ratio']);
export const marginDefaults = measure => RATIO_MEASURES.has(measure) ? {marginKind: 'relative', moe: '1/2'} : {marginKind: 'absolute', moe: '3/100'};
function precisionLines(state, point, sizes, sizeKey) {
  const {level = '19/20', precisionMeasure} = state;
  const defaults = marginDefaults(precisionMeasure);
  const kind = state.marginKind ?? defaults.marginKind;
  const moe = state.moe ?? defaults.moe;
  const assurance = String(state.assurance ?? '').trim();
  const margin = (kind === 'relative' ? 'relative_margin_of_error=' : 'margin_of_error=') + moe;
  const claim = assurance ? 'sample_size' : 'smallest_sample_size';
  return ['let precision = precision_target(at=' + point + ', level=' + level + ', ' + margin + (assurance ? ', assurance=' + assurance : '') + ')',
    'let sizes = ' + sizes,
    'let sizing = calculate(' + claim + '(candidates=sizes, target=precision))',
    'let n_needed = sizing.calculation.' + sizeKey];
}
// Whether the margin, assurance and level make a precision target, or what is wrong.
export function precisionPlannable(state) {
  const defaults = marginDefaults(state.precisionMeasure);
  const moe = state.moe ?? defaults.moe;
  const kind = state.marginKind ?? defaults.marginKind;
  if (!(eval_(moe) > 0)) return 'The margin of error must be a positive number, such as 3/100.';
  if (kind === 'relative' && RATIO_MEASURES.has(state.precisionMeasure) && !(eval_(moe) < 1)) return 'For a ratio, the relative margin must be below 1, such as 1/2.';
  const assurance = String(state.assurance ?? '').trim();
  if (assurance && !(eval_(assurance) > 0 && eval_(assurance) < 1)) return 'The assurance must lie between 0 and 1, such as 4/5, or be left blank.';
  return '';
}
// The intervals an observational design can plan, by its design and scales.
export function precisionMeasures(state) {
  const s = withObservedDefaults(state);
  if (s.outcomeScale !== 'binary' || (s.design === 'cross_sectional' && s.exposureScale !== 'binary')) {
    return s.design === 'cross_sectional' && s.outcomeScale === 'binary' ? {prevalence: {label: 'Prevalence', glyph: 'cross_sectional'}} : {};
  }
  return {
    cross_sectional: {prevalence: {label: 'Prevalence'}, prevalence_ratio: {label: 'Prevalence ratio'}, prevalence_difference: {label: 'Prevalence difference'}, odds_ratio: {label: 'Odds ratio'}},
    cohort: {cumulative_incidence: {label: 'Cumulative incidence'}, risk_ratio: {label: 'Risk ratio'}, risk_difference: {label: 'Risk difference'}, odds_ratio: {label: 'Odds ratio'}},
    case_control: {odds_ratio: {label: 'Odds ratio'}},
    matched_case_control: {conditional_odds_ratio: {label: 'Conditional odds ratio'}},
    person_time: {rate_ratio: {label: 'Rate ratio'}},
  }[s.design] || {};
}
export const precisionMeasure = state => {
  const measures = Object.keys(precisionMeasures(state));
  return measures.includes(state.precisionMeasure) ? state.precisionMeasure : measures[0];
};
// The planning fields of a precision target: one proportion, or the design's own point.
export const precisionFields = state => {
  const measure = precisionMeasure(state);
  if (['prevalence', 'cumulative_incidence'].includes(measure)) return [['base', 'Expected proportion', 'Such as 1/10.']];
  return PLAN_FIELDS[planKind(state.design || 'cohort', state.population)];
};
// The lines that plan an observational study's interval for a margin of error.
function observationalPrecision(state) {
  const {design = 'cohort', population = false, base = '1/10', ratio: r = '2', share = '3/10', exposedTime = '8000', unexposedTime = '24000',
    exposed = 100, unexposed = 200, cases = 100, controls = 200} = state;
  const s = withObservedDefaults(state);
  const measure = precisionMeasure(state);
  const normal = surveyed(s);
  const effect = normal ? ', design_effect=' + (state.deff ?? '2') : '';
  const single = ['prevalence', 'cumulative_incidence'].includes(measure);
  const group = measure === 'cumulative_incidence' && design === 'cohort' && !population ? ', group="exposed"' : '';
  const method = normal ? ', method="normal"' : '';
  const each = (first, second) => {
    const q = Number(second) / Number(first);
    return Number.isInteger(q) && q >= 1 && q <= 10 ? q : 1;
  };
  let point;
  let sizes = 'interval_sizes(interval=estimate, min_size=10, max_size=' + (normal ? 100000 : 20000) + ')';
  let sizeKey = 'total_sample_size';
  if (single) point = 'proportion(value=' + base + effect + ')';
  else if (design === 'matched_case_control') {
    point = 'discordant_pairs(share=' + share + ', odds_ratio=' + r + ')';
    sizeKey = 'pairs';
    sizes = 'interval_sizes(interval=estimate, min_size=10, max_size=10000)';
  } else if (design === 'person_time') {
    point = 'incidence_rates(rate_ratio=' + r + ', exposed_time=' + exposedTime + ', unexposed_time=' + unexposedTime + ')';
    sizeKey = 'events';
  } else if (design === 'case_control') {
    const q = each(cases, controls);
    point = 'exposure_prevalence(controls=' + base + ', odds_ratio=' + r + ')';
    sizes = 'interval_sizes(interval=estimate, min_size=10, max_size=' + Math.floor(20000 / (1 + q)) + ', ratio=' + q + ')';
    sizeKey = 'cases';
  } else if (design === 'cohort' && !population) {
    const q = each(exposed, unexposed);
    point = 'risks(unexposed=' + base + ', risk_ratio=' + r + ')';
    sizes = 'interval_sizes(interval=estimate, min_size=10, max_size=' + Math.floor(20000 / (1 + q)) + ', ratio=' + q + ')';
    sizeKey = 'exposed';
  } else {
    point = design === 'cohort' ?
      'risks(unexposed=' + base + ', risk_ratio=' + r + ', exposed_share=' + share + ')' :
      'outcome_prevalence(unexposed=' + base + ', prevalence_ratio=' + r + ', exposed_share=' + share + effect + ')';
  }
  return ['let estimate = planned_interval(model=study, measure="' + measure + '"' + method + group + ')',
    ...precisionLines({...state, precisionMeasure: measure}, point, sizes, sizeKey)];
}

export const RULES = {
  threshold: {label: 'Count thresholds', detail: 'Continue if enough respond at stage one.', glyph: 'stages'},
  posterior: {label: 'Posterior probabilities', detail: 'Continue while the posterior is promising.', glyph: 'prior'},
};
export function twoStageSource({name = 'study', rule = 'threshold', find = 'search', criterion = 'optimal', nullRate = '1/5', target = '2/5', alpha = '1/20',
  maxTotal = 45, n1 = 13, n2 = 30, continueAbove = 3, rejectAbove = 12, priorA = 1, priorB = 1, continueAt = '1/2', successAt = '19/20'}) {
  const head = ['# ' + name + ': a single-arm design in two stages, tested at a response rate of ' + nullRate + '.', 'use designs.two_stage', 'use planning', ''];
  const goal = 'let target = power_target(at=response_rate(value=' + target + '), minimum=4/5, maximum_typeI=' + alpha + ')';
  if (rule === 'threshold' && find === 'search') {
    return {source: finish([...head, goal,
      'let candidates = two_stage_designs(null_rate=' + nullRate + ', max_total=' + maxTotal + ', criterion="' + criterion + '")',
      'let sizing = sample_size(candidates=candidates, target=target)',
      'let recommendation = calculate(sizing)', 'let checked = verify(sizing)',
      'let stage1 = recommendation.calculation.n_stage1', 'let stage2 = recommendation.calculation.n_stage2', '']),
    test: 'two_stage_designs', evidence: 'proved', notes: ['The chosen design is certified; the ranking is a calculation.']};
  }
  const decide = rule === 'posterior' ?
    ['let prior = beta_prior(a=' + priorA + ', b=' + priorB + ')',
      'let rule = posterior_rule(prior=prior, reference=' + nullRate + ', continue_at_least=' + continueAt + ', success_at_least=' + successAt + ')'] :
    ['let rule = threshold_rule(continue_above=' + continueAbove + ', reject_above=' + rejectAbove + ')'];
  return {source: finish([...head, 'let stages = two_stage_binomial(n_stage1=' + n1 + ', n_stage2=' + n2 + ')', ...decide,
    'let analysis = two_stage_test(design=stages, rule=rule, null_rate=' + nullRate + ')', goal,
    'let claim = meets(analysis=analysis, target=target)', 'let characteristics = calculate(claim)', 'let checked = verify(claim)', '']),
  test: 'two_stage_test', evidence: 'proved',
  notes: rule === 'posterior' ? ['A posterior threshold does not bound Type I error by itself: the check does.'] : []};
}

// Observational studies --------------------------------------------------------------------
// What an observational design is planned at: the reference probability, the measure the
// design estimates, and for a design that fixes only its total, the share exposed.
export const PLAN_FIELDS = {
  case_control: [['base', 'Exposed among controls', 'Such as 1/5.'], ['ratio', 'Odds ratio', 'The odds of exposure, cases over controls.']],
  cohort: [['base', 'Risk without exposure', 'Such as 1/10.'], ['ratio', 'Risk ratio', 'Exposed over unexposed.']],
  population: [['base', 'Risk without exposure', 'Such as 1/10.'], ['ratio', 'Risk ratio', 'Exposed over unexposed.'], ['share', 'Share exposed', 'The probability that a participant is exposed.']],
  cross_sectional: [['base', 'Prevalence without exposure', 'Such as 1/10.'], ['ratio', 'Prevalence ratio', 'Exposed over unexposed.'], ['share', 'Share exposed', 'The probability that a participant is exposed.']],
  matched_case_control: [['share', 'Discordant pairs', 'The share with exactly one exposed, such as 1/4.'], ['ratio', 'Conditional odds ratio', 'Such as 2.']],
  person_time: [['ratio', 'Rate ratio', 'Exposed over unexposed.'], ['exposedTime', 'Exposed person-time', 'Such as person-years.'], ['unexposedTime', 'Unexposed person-time', 'Such as person-years.']],
  // Cited tests of two measured variables, planned at a correlation or a slope.
  correlation: [['rho', 'Correlation', 'Between the two variables, such as 1/5.']],
  outcome_means: [['meanUnexposed', 'Mean without exposure', 'Such as 120.'], ['meanExposed', 'Mean with exposure', 'Such as 125.'],
    ['outcomeSd', 'Standard deviation', 'Of the outcome about the group means.']],
  outcome_means_share: [['meanUnexposed', 'Mean without exposure', 'Such as 120.'], ['meanExposed', 'Mean with exposure', 'Such as 125.'],
    ['outcomeSd', 'Standard deviation', 'Of the outcome about the group means.'], ['share', 'Share exposed', 'The probability that a participant is exposed.']],
  odds_per_sd: [['ratio', 'Odds ratio per SD', 'For one standard deviation more of the exposure, such as 3/2.'],
    ['base', 'Outcome probability', 'At the exposure\'s mean, such as 1/10.']],
  slope: [['slopeValue', 'Slope', 'Change in the outcome per unit of exposure.'], ['exposureSd', 'Exposure SD', 'The spread of the exposure.'],
    ['residualSd', 'Residual SD', 'The outcome\'s spread about the line.']],
};
export const planKind = (design, population) => design === 'cohort' && population ? 'population' : design;
// The planning fields of the chosen test: the design's, or the cited test's own point.
// A survey test of a complex sample is planned with the survey's design effect.
export const needsDesignEffect = state => {
  const s = withObservedDefaults(state);
  return OBSERVED_TESTS[observedTest(s)]?.module === 'tests.survey' && surveyed(s);
};
// Pearson's test and the slope test, without covariates, can be simulated with skewed data.
export const skewable = state => {
  const s = withObservedDefaults(state);
  return ['pearson_correlation', 'linear_association'].includes(observedTest(s)) &&
    ['correlation', 'slope'].includes(observedPlanKind(s)) &&
    !(OBSERVED_TESTS[observedTest(s)]?.covariates && String(s.covariates ?? 'age, sex').split(',').map(c => c.trim()).filter(Boolean).length);
};
export const observedPlanKind = state => {
  const s = withObservedDefaults(state);
  const test = observedTest(s);
  if (['logistic_association', 'survey_logistic'].includes(test) && continuousExposure(s)) return 'odds_per_sd';
  if (['linear_association', 'survey_linear'].includes(test)) {
    if (continuousExposure(s)) return 'slope';
    // A yes-or-no exposure: the two groups' means, and the share exposed when only the total is fixed.
    return s.design === 'cohort' && !s.population ? 'outcome_means' : 'outcome_means_share';
  }
  return ['pearson_correlation', 'spearman_correlation'].includes(test) ? 'correlation' : planKind(s.design, s.population);
};

// Whether a planning point is usable, or what is wrong with it.
export function observationalPlannable(state) {
  const {design = 'cohort', population = false, base = '1/10', ratio: r = '2', share = '3/10', exposedTime = '8000', unexposedTime = '24000',
    rho = '1/5', slopeValue = '1/2', exposureSd = '4', residualSd = '15', deff = '2'} = state;
  const cited = observedPlanKind(state);
  if (needsDesignEffect(state) && !(eval_(deff) > 0)) return 'The design effect must be a positive number, such as 2.';
  if (cited === 'correlation') {
    const value = eval_(rho);
    if (!(Number.isFinite(value) && value > -1 && value < 1)) return 'The correlation must lie between -1 and 1, such as 1/5.';
    return value === 0 ? 'A correlation of 0 is no association: there would be nothing to detect.' : '';
  }
  if (cited === 'slope') {
    if (!Number.isFinite(eval_(slopeValue)) || eval_(slopeValue) === 0) return 'The slope must be a number other than 0, such as 1/2.';
    return eval_(exposureSd) > 0 && eval_(residualSd) > 0 ? '' : 'Each standard deviation must be a positive number, such as 4.';
  }
  if (cited === 'outcome_means' || cited === 'outcome_means_share') {
    const {meanUnexposed = '120', meanExposed = '125', outcomeSd = '15'} = state;
    if (!Number.isFinite(eval_(meanUnexposed)) || !Number.isFinite(eval_(meanExposed))) return 'Each mean must be a number, such as 120.';
    if (eval_(meanUnexposed) === eval_(meanExposed)) return 'The two means cannot be equal: there would be nothing to detect.';
    if (!(eval_(outcomeSd) > 0)) return 'The standard deviation must be a positive number, such as 15.';
    if (cited === 'outcome_means_share' && !(eval_(share) > 0 && eval_(share) < 1)) return 'The share must lie between 0 and 1, such as 3/10.';
    return '';
  }
  if (cited === 'odds_per_sd') {
    if (!(eval_(base) > 0 && eval_(base) < 1)) return 'The outcome probability must lie between 0 and 1, such as 1/10.';
    if (!(eval_(r) > 0)) return 'The odds ratio must be a positive number, such as 3/2.';
    return eval_(r) === 1 ? 'An odds ratio of 1 is no association: there would be nothing to detect.' : '';
  }
  const kind = planKind(design, population);
  const wanted = PLAN_FIELDS[kind].map(([key]) => key);
  const values = {base: eval_(base), ratio: eval_(r), share: eval_(share)};
  const inside = value => Number.isFinite(value) && value > 0 && value < 1;
  if (wanted.includes('base') && !inside(values.base)) return 'The probability without exposure must lie between 0 and 1, such as 1/10.';
  if (!(Number.isFinite(values.ratio) && values.ratio > 0)) return 'The ratio must be a positive number, such as 2.';
  if (values.ratio === 1) return 'A ratio of 1 is no association: there would be nothing to detect.';
  if (wanted.includes('share') && !inside(values.share)) return 'The share must lie between 0 and 1, such as 3/10.';
  if (kind === 'person_time' && !(eval_(exposedTime) > 0 && eval_(unexposedTime) > 0)) return 'Each person-time must be a positive number, such as 8000.';
  if (['cohort', 'population', 'cross_sectional'].includes(kind) && values.base * values.ratio > 1) {
    return 'That ratio makes the probability with exposure above 1.';
  }
  return '';
}

const continuousOutcome = s => s.design !== 'case_control' && s.design !== 'matched_case_control' && s.design !== 'person_time' && s.outcomeScale === 'continuous';
const continuousExposure = s => s.design === 'cross_sectional' && s.exposureScale === 'continuous';
const surveyed = s => s.design === 'cross_sectional' && s.survey && s.survey !== 'simple_random';
const tableDesign = s => ['cohort', 'case_control', 'cross_sectional'].includes(s.design);
const withObservedDefaults = s => ({design: 'cohort', outcomeScale: 'binary', exposureScale: 'binary', survey: 'simple_random', ...s});
// The tests an observational design can use, proved first.
export const OBSERVED_TESTS = {
  fisher_exact: {label: "Fisher's exact test", module: 'tests.association', evidence: 'proved',
    fits: s => tableDesign(s) && !continuousOutcome(s) && !continuousExposure(s) && !surveyed(s)},
  mcnemar: {label: "McNemar's exact test", module: 'tests.association', evidence: 'proved', fits: s => s.design === 'matched_case_control'},
  rate_test: {label: 'Exact rate test', detail: 'Equal incidence rates, given the events.', module: 'tests.association', evidence: 'proved', fits: s => s.design === 'person_time'},
  logistic_association: {label: 'Logistic regression', module: 'tests.regression', evidence: 'cited', covariates: true,
    fits: s => tableDesign(s) && !continuousOutcome(s) && !surveyed(s)},
  modified_poisson: {label: 'Modified Poisson regression', detail: 'A risk or prevalence ratio.', module: 'tests.regression', evidence: 'cited', covariates: true,
    fits: s => (s.design === 'cohort' || s.design === 'cross_sectional') && !continuousOutcome(s) && !surveyed(s)},
  conditional_logistic: {label: 'Conditional logistic regression', module: 'tests.regression', evidence: 'cited', covariates: true, fits: s => s.design === 'matched_case_control'},
  poisson_rate_regression: {label: 'Poisson rate regression', module: 'tests.regression', evidence: 'cited', covariates: true, fits: s => s.design === 'person_time'},
  linear_association: {label: 'Linear regression', module: 'tests.regression', evidence: 'cited', covariates: true,
    fits: s => (s.design === 'cohort' || s.design === 'cross_sectional') && continuousOutcome(s) && !surveyed(s)},
  pearson_correlation: {label: "Pearson's correlation", module: 'tests.correlation', evidence: 'cited',
    fits: s => s.design === 'cross_sectional' && continuousOutcome(s) && continuousExposure(s) && !surveyed(s)},
  spearman_correlation: {label: "Spearman's rank correlation", detail: 'Exact permutation test.', module: 'tests.correlation', evidence: 'cited',
    fits: s => s.design === 'cross_sectional' && continuousOutcome(s) && continuousExposure(s) && !surveyed(s)},
  rao_scott_test: {label: 'Rao-Scott test', detail: 'A 2x2 table from a survey.', module: 'tests.survey', evidence: 'cited',
    fits: s => surveyed(s) && !continuousOutcome(s) && !continuousExposure(s)},
  survey_logistic: {label: 'Survey logistic regression', module: 'tests.survey', evidence: 'cited', covariates: true, fits: s => surveyed(s) && !continuousOutcome(s)},
  survey_linear: {label: 'Survey linear regression', module: 'tests.survey', evidence: 'cited', covariates: true, fits: s => surveyed(s) && continuousOutcome(s)},
};
export const observedTests = state => Object.keys(OBSERVED_TESTS).filter(id => OBSERVED_TESTS[id].fits(withObservedDefaults(state)));
export const observedTest = state => observedTests(state).includes(state.test) ? state.test : observedTests(state)[0];
export const SURVEYS = {
  simple_random: {label: 'Simple random'}, stratified: {label: 'Stratified'}, cluster: {label: 'In clusters'}, weighted: {label: 'Weighted'},
};
export function observedExtras(state) {
  const s = withObservedDefaults(state);
  const test = observedTest(s);
  const proved = ['fisher_exact', 'mcnemar', 'rate_test'].includes(test);
  // Pearson's correlation, the slope of a measured exposure and the regressions with a
  // published formula can be planned too.
  // Every cited observational test has a power formula.
  const cited = OBSERVED_TESTS[test].evidence === 'cited';
  return {plan: proved || cited, data: proved, precision: Object.keys(precisionMeasures(state)).length > 0};
}

// A 2x2 table, pairs or events that fit what the design fixed, for a first look at results.
export function defaultTable({design = 'cohort', population = false, exposed = 100, unexposed = 200, cases = 100, controls = 200, total = 400}) {
  const round = x => Math.round(x);
  if (design === 'case_control') {
    const ec = round(cases * 0.4); const en = round(controls * 0.25);
    return {exposedCases: ec, exposedNoncases: en, unexposedCases: cases - ec, unexposedNoncases: controls - en};
  }
  let e = Number(exposed); let u = Number(unexposed);
  if (design === 'cross_sectional' || population) { e = round(total * 0.3); u = total - e; }
  const ec = round(e * 0.2); const uc = round(u * 0.1);
  return {exposedCases: ec, exposedNoncases: e - ec, unexposedCases: uc, unexposedNoncases: u - uc};
}
export function defaultPairs({cases = 100}) {
  const p = Number(cases);
  const both = Math.round(p * 0.1); const caseOnly = Math.round(p * 0.15); const controlOnly = Math.round(p * 0.08);
  return {bothExposed: both, caseExposedOnly: caseOnly, controlExposedOnly: controlOnly, neitherExposed: p - both - caseOnly - controlOnly};
}

// The lines that find a sample size for an observational design, by exact power.
function observationalPlan(state) {
  const {design, population, base, ratio: r, share, cases, controls, exposed, unexposed, alpha, exposedTime = '8000', unexposedTime = '24000',
    rho = '1/5', slopeValue = '1/2', exposureSd = '4', residualSd = '15', adjusted = []} = state;
  const kind = planKind(design, population);
  const target = 'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + alpha + ')';
  const cited = observedPlanKind(state);
  // A cited test's formula is cheap, so it may search far beyond the exact tests' limits.
  const scale = state.citedTest ? 100 : 1;
  // A survey test of a complex sample is planned with its design effect.
  const effect = state.surveyTest && surveyed(withObservedDefaults(state)) ? ', design_effect=' + (state.deff ?? '2') : '';
  if (cited === 'outcome_means' || cited === 'outcome_means_share') {
    const {meanUnexposed = '120', meanExposed = '125', outcomeSd = '15'} = state;
    const shared = cited === 'outcome_means_share' ? ', exposed_share=' + share : '';
    const point = 'outcome_means(unexposed=' + meanUnexposed + ', exposed=' + meanExposed + ', sd=' + outcomeSd + shared + effect + ')';
    const each = Number(unexposed) / Number(exposed);
    const q = Number.isInteger(each) && each >= 1 && each <= 10 ? each : 1;
    return ['let expected = ' + point, target,
      cited === 'outcome_means' ?
        'let sizes = cohort_sizes(analysis=analysis, min_exposed=10, max_exposed=' + Math.floor(100000 / (1 + q)) + ', unexposed_per_exposed=' + q + ')' :
        'let sizes = total_sizes(analysis=analysis, min_n=' + (adjusted.length + 3) + ', max_n=100000)',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let n_needed = sizing.calculation.total_sample_size'];
  }
  if (cited === 'correlation' || cited === 'slope' || cited === 'odds_per_sd') {
    // Skewed data are simulated, for Pearson's test and the slope test without covariates.
    const skews = skewable(state) ? [['skewY', 'skewness'], ['skewX', 'exposure_skewness']]
      .filter(([key]) => String(state[key] ?? '').trim() !== '' && eval_(state[key]) !== 0)
      .map(([key, name]) => ', ' + name + '=' + String(state[key]).trim()).join('') : '';
    const point = cited === 'correlation' ? 'correlation(value=' + rho + skews + ')' :
      cited === 'odds_per_sd' ? 'odds_per_sd(odds_ratio=' + r + ', baseline=' + base + effect + ')' :
        'slope(value=' + slopeValue + ', exposure_sd=' + exposureSd + ', residual_sd=' + residualSd + effect + skews + ')';
    if (skews) {
      return ['# Skewed data: power is simulated, and Type I is judged against 1.5 times alpha.', 'let expected = ' + point,
        'let target = power_target(at=expected, minimum=4/5, maximum_typeI=' + times(alpha, 3, 2) + ')',
        '# Every participant is drawn: 2,000 runs and totals up to 300 keep the search quick.',
        'let sizes = total_sizes(analysis=analysis, min_n=4, max_n=300)',
        'let sizing = simulate(smallest_sample_size(candidates=sizes, target=target), seed=' + (state.seed ?? 2026) + ', runs=2000)',
        'let n_needed = sizing.calculation.total_sample_size'];
    }
    return ['let expected = ' + point, target,
      'let sizes = total_sizes(analysis=analysis, min_n=' + (adjusted.length + 3) + ', max_n=100000)',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let n_needed = sizing.calculation.total_sample_size'];
  }
  const each = (first, second) => {
    const q = Number(second) / Number(first);
    return Number.isInteger(q) && q >= 1 && q <= 10 ? q : 1;
  };
  if (kind === 'person_time') {
    return ['let expected = incidence_rates(rate_ratio=' + r + ', exposed_time=' + exposedTime + ', unexposed_time=' + unexposedTime + ')', target,
      'let sizes = event_counts(analysis=analysis, min_events=10, max_events=' + 500 * scale + ')',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let events_needed = sizing.calculation.events'];
  }
  if (kind === 'matched_case_control') {
    return ['let expected = discordant_pairs(share=' + share + ', odds_ratio=' + r + ')', target,
      'let sizes = matched_sizes(analysis=analysis, min_pairs=10, max_pairs=' + 400 * scale + ')',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let pairs_needed = sizing.calculation.pairs'];
  }
  if (kind === 'case_control') {
    const q = each(cases, controls);
    return ['let expected = exposure_prevalence(controls=' + base + ', odds_ratio=' + r + ')', target,
      'let sizes = case_control_sizes(analysis=analysis, min_cases=10, max_cases=' + (state.citedTest ? Math.floor(100000 / (1 + q)) : Math.floor(500 / q)) + ', controls_per_case=' + q + ')',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let cases_needed = sizing.calculation.cases'];
  }
  if (kind === 'cohort') {
    const q = each(exposed, unexposed);
    return ['let expected = risks(unexposed=' + base + ', risk_ratio=' + r + ')', target,
      'let sizes = cohort_sizes(analysis=analysis, min_exposed=10, max_exposed=' + (state.citedTest ? Math.floor(100000 / (1 + q)) : Math.floor(500 / q)) + ', unexposed_per_exposed=' + q + ')',
      'let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))',
      'let exposed_needed = sizing.calculation.exposed'];
  }
  const point = kind === 'population' ?
    'risks(unexposed=' + base + ', risk_ratio=' + r + ', exposed_share=' + share + ')' :
    'outcome_prevalence(unexposed=' + base + ', prevalence_ratio=' + r + ', exposed_share=' + share + effect + ')';
  return ['let expected = ' + point, target,
    'let sizes = total_sizes(analysis=analysis, min_n=10, max_n=' + 150 * scale + ')',
    'let sizing = calculate(' + (state.citedTest ? 'smallest_sample_size' : 'sample_size') + '(candidates=sizes, target=target))',
    'let total_needed = sizing.calculation.total_sample_size'];
}

// An observational study: its design, the test of association, and when asked, the smallest
// size with 80% power by exact calculation, or the analysis of observed results.
export function observationalSource(state) {
  const {name = 'study', design = 'cohort', exposure = 'exposure', outcome = 'outcome', exposed = 100, unexposed = 200, cases = 100, controls = 200,
    total = 400, population = false, alpha = '1/20', outcomeScale = 'binary', exposureScale = 'binary', survey = 'simple_random', clusters = 100,
    covariates = 'age, sex', exposedEvents = 20, exposedTime = '8000', unexposedEvents = 30, unexposedTime = '24000'} = state;
  const s = withObservedDefaults({...state, design, outcomeScale, exposureScale, survey});
  const test = observedTest(s);
  const info = OBSERVED_TESTS[test];
  const extras = observedExtras(s);
  const add = state.add || (state.plan ? 'plan' : 'none');
  const planning = add === 'plan' && extras.plan;
  const analysing = add === 'data' && extras.data;
  const named = ', exposure=' + quoted(exposure) + ', outcome=' + quoted(outcome);
  const scales = (continuousExposure(s) ? ', exposure_scale="continuous"' : '') + (continuousOutcome(s) ? ', outcome_scale="continuous"' : '');
  const declared = design === 'matched_case_control' ? 'matched_case_control(pairs=' + cases + named + ')' :
    design === 'person_time' ? 'person_time_cohort(exposure=' + quoted(exposure) + ', outcome=' + quoted(outcome) + ')' :
      design === 'case_control' ? 'case_control(cases=' + cases + ', controls=' + controls + named + ')' :
        design === 'cross_sectional' ? 'cross_sectional(n=' + total + named + scales +
          (surveyed(s) ? ', survey="' + survey + '"' + (survey === 'cluster' ? ', clusters=' + clusters : '') : '') + ')' :
          population ? 'cohort(n=' + total + named + scales + ')' : 'cohort(exposed=' + exposed + ', unexposed=' + unexposed + named + scales + ')';
  const adjusted = info.covariates ? String(covariates).split(',').map(c => c.trim()).filter(Boolean) : [];
  const precise = add === 'precision' && extras.precision;
  const uses = ['models.observational', 'sampling', info.module, ...(planning || precise ? ['planning'] : []), ...(analysing ? ['estimation.observational'] : [])];
  const question = design === 'matched_case_control' ? 'within matched pairs?' : design === 'person_time' ? 'do their incidence rates differ?' : 'associated?';
  const lines = ['# ' + name + ': are ' + exposure + ' and ' + outcome + ' ' + question, ...uses.map(m => 'use ' + m), '',
    'let study = ' + declared, 'let design = fixed(model=study)', 'let null = no_association(model=study)',
    'let analysis = ' + test + '(design=design, null=null, alpha=' + alpha + (adjusted.length ? ', adjusted_for=[' + adjusted.map(quoted).join(', ') + ']' : '') + ')',
    'let checked = verify(typeI(analysis))', ''];
  const citedPlan = planning && info.evidence === 'cited';
  if (planning) {
    lines.push(citedPlan ? '# The smallest total with 80% power at the expected association, for normal variables.' :
      '# The smallest size with 80% power at the expected association: exact, calculated.',
    ...observationalPlan({...state, design, population, alpha, ratio: state.ratio ?? '2', base: state.base ?? '1/10', share: state.share ?? '3/10',
      cases, controls, exposed, unexposed, exposedTime, unexposedTime, adjusted, citedTest: citedPlan, surveyTest: info.module === 'tests.survey'}), '');
  }
  if (precise) {
    lines.push('# How many for the margin of error you want: ' + (surveyed(s) ? 'the normal interval, with the design effect.' : 'StatClaim\'s exact interval.'),
      ...observationalPrecision({...state, design, population}), '');
  }
  if (analysing) {
    if (design === 'matched_case_control') {
      const p = {...defaultPairs({cases}), ...(state.pairs || {})};
      lines.push('# The observed pairs, by who was exposed.',
        'let seen = observed_pairs(model=study, both_exposed=' + p.bothExposed + ', case_exposed_only=' + p.caseExposedOnly +
          ', control_exposed_only=' + p.controlExposedOnly + ', neither_exposed=' + p.neitherExposed + ')',
        'let outcome_test = verify(matched_result(analysis=analysis, pairs=seen))',
        'let odds = verify(conditional_odds_ratio(pairs=seen, level=19/20))', '');
    } else if (design === 'person_time') {
      lines.push('# The observed events and person-time.',
        'let seen = observed_events(model=study, exposed_events=' + exposedEvents + ', exposed_time=' + exposedTime +
          ', unexposed_events=' + unexposedEvents + ', unexposed_time=' + unexposedTime + ')',
        'let outcome_test = verify(rate_result(analysis=analysis, events=seen))',
        'let rates = verify(rate_ratio(events=seen, level=19/20))', '');
    } else {
      const t = {...defaultTable({design, population, exposed, unexposed, cases, controls, total}), ...(state.table || {})};
      const measure = design === 'cross_sectional' ? 'prevalence_ratio' : design === 'cohort' ? 'risk_ratio' : null;
      lines.push('# The observed 2x2 table.',
        'let seen = observed_table(model=study, exposed_cases=' + t.exposedCases + ', exposed_noncases=' + t.exposedNoncases +
          ', unexposed_cases=' + t.unexposedCases + ', unexposed_noncases=' + t.unexposedNoncases + ')',
        'let outcome_test = verify(association_result(analysis=analysis, table=seen))',
        'let odds = verify(odds_ratio(table=seen, level=19/20))',
        ...(measure ? ['let ' + measure.split('_')[0] + 's = verify(' + measure + '(table=seen, level=19/20))'] : []), '');
    }
  }
  const notes = [];
  if (info.evidence === 'proved') notes.push('It concerns association, not an effect of the exposure.');
  if (precise) notes.push('The size comes from the interval\'s precision, calculated; Lean does not check precision.');
  if (citedPlan) notes.push('The sample size comes from power under normality, calculated; a cited test\'s power cannot be verified.');
  else if (planning) notes.push('The sample size comes from exact power, calculated; verify the sizing to have Lean check it.');
  return {source: finish(lines), test, evidence: info.evidence, question: 'associated', notes};
}

// The source for any flow.
export const FLOWS = {trial: studySource, several: severalSource, interim: interimSource, one_arm: oneArmSource, two_stage: twoStageSource, observed: observationalSource};
export const TEST_WORDS = {
  ...Object.fromEntries(Object.entries(OBSERVED_TESTS).map(([id, t]) => [id, t.label])),
  fisher: "Fisher's exact test", fisher_one_sided: "One-sided Fisher's exact test", difference_test: 'Exact difference test',
  t_test: 'Pooled-variance t-test', t_test_one_sided: 'One-sided pooled-variance t-test', welch_test: 'Welch t-test', welch_test_one_sided: 'One-sided Welch t-test',
  mmrm_test: 'Mixed model for repeated measures', mmrm_test_one_sided: 'One-sided mixed model for repeated measures', log_rank: 'Log-rank test',
  cluster_t_test: 'Cluster-level t-test', cluster_proportion_t_test: 'Cluster-level t-test of proportions', randomisation_test: 'Randomisation test',
  logistic_regression: 'Logistic regression', logistic_regression_one_sided: 'One-sided logistic regression', declared_test: 'Your declared test',
  bonferroni: 'Bonferroni family', fixed_sequence: 'Fixed sequence', graphical: 'Graphical procedure', alpha_spending: 'Interim look with alpha spending',
  binomial_test: 'One-sided exact binomial test', confidence_interval: 'Exact confidence interval', two_stage_designs: 'Two-stage design search', two_stage_test: 'Two-stage design',
  fisher_exact: "Fisher's exact test of association", mcnemar: "McNemar's exact test for matched pairs", rate_test: 'Exact test of equal incidence rates',
};
