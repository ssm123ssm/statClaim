// New study: pick a design, answer a few questions, and get a study that compiles.
// designs.js holds the catalogue and builds the source; this file is the dialog.
import { el, button, icon, certStamp } from './ui.js';
import {
  FAMILIES, DESIGNS, designById, EVIDENCE, OUTCOMES, QUESTIONS, available, TRIAL_TESTS, trialTests, trialTest, trialExtras,
  plannable, ratesPlannable, PROCEDURES, SPENDING, AIMS, RULES, PLAN_FIELDS, planKind, observedPlanKind, needsDesignEffect, observationalPlannable, skewable,
  MARGIN_KINDS, marginDefaults, precisionPlannable, precisionMeasures, precisionMeasure, precisionFields,
  ratio, OBSERVED_TESTS, observedTests, observedTest, observedExtras, SURVEYS, defaultTable, defaultPairs, FLOWS, TEST_WORDS,
  studyName, fraction, isShare, isWhole, eval_, times,
} from './designs.js';
export {
  studySource, observationalSource, severalSource, interimSource, oneArmSource, twoStageSource,
  available, plannable, observationalPlannable, PLAN_FIELDS, studyName, DESIGNS, FAMILIES,
} from './designs.js';

// Small drawings for tiles and cards, on the same 20-unit grid as the icons in ui.js.
const GLYPHS = {
  trial: 'M3 6h3l8 8h3M3 14h3l8-8h3M15 4l2 2-2 2M15 12l2 2-2 2',
  cohort: 'M4.5 8a2 2 0 100 4 2 2 0 000-4zM8 10h8.5M13 6.5l3.5 3.5-3.5 3.5',
  case_control: 'M15.5 8a2 2 0 100 4 2 2 0 000-4zM12 10H3.5M7 6.5L3.5 10 7 13.5',
  cross_sectional: 'M3 6.5h3l1.5-2h5L14 6.5h3v9H3zM10 8.5a2.5 2.5 0 100 5 2.5 2.5 0 000-5z',
  matched_case_control: 'M6.5 7a3 3 0 100 6 3 3 0 000-6zM13.5 7a3 3 0 100 6 3 3 0 000-6zM9.5 10h1',
  person_time: 'M10 3.5a6.5 6.5 0 100 13 6.5 6.5 0 000-13zM10 6.5V10l3 2',
  binary: 'M2.5 10.5l2.5 2.5 4.5-5M12 7.5l5 5M17 7.5l-5 5',
  continuous: 'M2.5 13.5L13 3l4 4L6.5 17.5zM6 10l1.5 1.5M8.5 7.5l1.5 1.5M11 5l1.5 1.5',
  repeated: 'M3.5 5h13v11.5h-13zM3.5 8.5h13M7 3v3.5M13 3v3.5M7 12h.01M10 12h.01M13 12h.01',
  survival: 'M5.5 3h9M5.5 17h9M7 3c0 4 6 4.5 6 7s-6 3-6 7M13 3c0 4-6 4.5-6 7s6 3 6 7',
  differ: 'M3 10h14M6 7l-3 3 3 3M14 7l3 3-3 3',
  better: 'M10 16V4M6 8l4-4 4 4',
  margin: 'M2.5 15.5h2.5M8 15.5h4M15 15.5h2.5M10 12.5V3.5M6.5 7L10 3.5 13.5 7',
  higher: 'M10 16V4M6 8l4-4 4 4',
  lower: 'M10 4v12M6 12l4 4 4-4',
  groups: 'M3 5h6v10H3zM11 5h6v10h-6z',
  population: 'M10 3a7 7 0 100 14 7 7 0 000-14zM7.5 8h.01M12.5 8.5h.01M10 11h.01M7 12.5h.01M13 12.5h.01',
  participants: 'M10 3.5a3 3 0 100 6 3 3 0 000-6zM4 17c0-3.5 2.7-5.5 6-5.5s6 2 6 5.5',
  clusters: 'M3 17V7.5l7-4.5 7 4.5V17zM8 17v-4h4v4M10 6.5v3.5M8.25 8.25h3.5',
  book: 'M3 4.5c2.5-1 5-1 7 .5 2-1.5 4.5-1.5 7-.5v11c-2.5-1-5-1-7 .5-2-1.5-4.5-1.5-7-.5z M10 5v11',
  dice: 'M5 3.5h10a1.5 1.5 0 011.5 1.5v10a1.5 1.5 0 01-1.5 1.5H5A1.5 1.5 0 013.5 15V5A1.5 1.5 0 015 3.5zM7 7h.01M13 13h.01M10 10h.01M13 7h.01M7 13h.01',
  blocks: 'M3 3.5h6v6H3zM11 3.5h6v6h-6zM3 11.5h6v5H3zM11 11.5h6v5h-6z',
  cluster: 'M3 17V7.5l7-4.5 7 4.5V17zM8 17v-4h4v4M10 6.5v3.5M8.25 8.25h3.5',
  visits: 'M3.5 5h13v11.5h-13zM3.5 8.5h13M7 3v3.5M13 3v3.5M7 12h.01M10 12h.01M13 12h.01',
  pencil: 'M12.5 4.5l3 3L7 16H4v-3z',
  several: 'M4.5 16V10M8.5 16V5M12.5 16V8M16.5 16v-4M3 16h15',
  sequence: 'M4.5 8a2 2 0 100 4 2 2 0 000-4zM10 8a2 2 0 100 4 2 2 0 000-4zM15.5 8a2 2 0 100 4 2 2 0 000-4zM6.5 10h1.5M12 10h1.5',
  graph: 'M5 3.5a2 2 0 100 4 2 2 0 000-4zM15 3.5a2 2 0 100 4 2 2 0 000-4zM10 12.5a2 2 0 100 4 2 2 0 000-4zM7 5.5h6M6 7.3l3 5.4M14 7.3l-3 5.4',
  looks: 'M10 5.5a6 6 0 100 12 6 6 0 000-12zM10 8.5v3l2 1.5M8 2.5h4M10 2.5v3',
  single: 'M10 3.5a3 3 0 100 6 3 3 0 000-6zM4 17c0-3.5 2.7-5.5 6-5.5s6 2 6 5.5',
  interval: 'M3 10h14M3 7v6M17 7v6M10 8.5a1.5 1.5 0 100 3 1.5 1.5 0 000-3z',
  stages: 'M3 16h4.5v-4.5H12V7h5M3 16h14',
  prior: 'M2.5 16c3 0 4-10 7.5-10s4.5 10 7.5 10M2.5 16h15',
  adjust: 'M4 5h12M4 10h12M4 15h12M7 3.5v3M13 8.5v3M9 13.5v3',
  correlation: 'M3 17L17 3M5.5 13.5h.01M8 12.5h.01M7.5 9.5h.01M11 9h.01M12 6h.01M14.5 7.5h.01M10.5 13h.01',
  survey: 'M5.5 4h9v13h-9zM8 2.5h4v3H8zM8 9.5l1.5 1.5 2.5-3M8 14h4',
  target: 'M10 3v3m0 8v3M3 10h3m8 0h3M10 7a3 3 0 100 6 3 3 0 000-6z',
  table: 'M3 4h14v12H3zM3 8h14M3 12h14M10 4v12',
  none: 'M5 10h10',
  search: 'M8.5 3.5a5 5 0 100 10 5 5 0 000-10zM12.2 12.2L17 17',
  link: 'M8.5 11.5l3-3M7 9L5.5 10.5a2.5 2.5 0 003.5 3.5L10.5 12.5M13 11l1.5-1.5a2.5 2.5 0 00-3.5-3.5L9.5 7.5',
};
export function glyph(name) {
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('viewBox', '0 0 20 20');
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('class', 'icon');
  const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  path.setAttribute('d', GLYPHS[name] || GLYPHS.differ);
  svg.append(path);
  return svg;
}
// A small badge for what a guarantee rests on: the medal for a proof, a book for a citation.
function seal(evidence) {
  const node = el('span', 'wizard-seal');
  node.dataset.evidence = evidence;
  node.title = EVIDENCE[evidence]?.label || '';
  node.append(evidence === 'proved' ? certStamp('cert-medal') : glyph({cited: 'book', declared: 'pencil', conditional: 'link'}[evidence] || 'book'));
  return node;
}

// One question per step. Each step wears the colour of the block it mostly shapes.
const STEPS = {
  kind: {label: 'Design', title: 'Which design?'},
  outcome: {label: 'Outcome', family: 'study', title: 'What do you measure in each participant?'},
  question: {label: 'Question', family: 'null', title: 'What do you want to know?'},
  test: {label: 'Test', family: 'analysis', title: 'How will you randomise and test?'},
  size: {label: 'Size', family: 'design', title: 'How many participants?'},
  outcomes: {label: 'Outcomes', family: 'study', title: 'Which outcomes?'},
  procedure: {label: 'Sharing', family: 'family', title: 'How is the level shared?'},
  looks: {label: 'Looks', family: 'design', title: 'When do you look?'},
  aim: {label: 'Question', family: 'null', title: 'What do you want to know about the rate?'},
  rule: {label: 'Rule', family: 'design', title: 'How does it decide?'},
  stages: {label: 'Stages', family: 'planning', title: 'Which stages?'},
  topic: {label: 'Topic', family: 'study', title: 'What are you studying?'},
  sampling: {label: 'Sampling', family: 'design', title: 'How were participants sampled?'},
  analysis: {label: 'Test', family: 'analysis', title: 'Which test?'},
  power: {label: 'Power', family: 'planning', title: 'How strict, and what else?'},
  name: {label: 'Name', family: 'run', title: 'Name your study'},
};
const ROUTES = {
  trial: ['kind', 'outcome', 'question', 'test', 'size', 'name'],
  several: ['kind', 'outcomes', 'procedure', 'size', 'name'],
  interim: ['kind', 'outcome', 'looks', 'name'],
  one_arm: ['kind', 'aim', 'size', 'name'],
  two_stage: ['kind', 'rule', 'stages', 'name'],
  observed: ['kind', 'topic', 'sampling', 'analysis', 'power', 'name'],
};
const TITLES = {one_arm: {size: 'How many, and at what rates?'}, several: {size: 'How many participants in each arm?'}};

// The blocks the study will have, coloured as the canvas colours them, by what each call makes.
const CALL_FAMILY = {};
for (const [family, names] of Object.entries({
  study: 'two_arm_binomial two_arm_continuous two_arm_survival two_arm assignment cluster_assignment binary_outcome continuous_outcome survival_outcome stratum one_arm_binomial two_stage_binomial cohort case_control cross_sectional matched_case_control person_time_cohort',
  design: 'fixed threshold_rule posterior_rule beta_prior',
  null: 'equal_proportions proportion_difference_at_most equal_means mean_difference_at_most mean_difference_at_least equal_survival no_effect no_association',
  family: 'bonferroni graphical fixed_sequence',
  run: 'verify calculate simulate',
  planning: 'binomial_rates mean_difference hazard_ratio exponential_survival correlation slope odds_per_sd outcome_means risks outcome_prevalence exposure_prevalence discordant_pairs incidence_rates response_rate power_target equal_arm_sizes cluster_counts cluster_sizes cohort_sizes case_control_sizes total_sizes matched_sizes event_counts sample_sizes two_stage_designs',
  claim: 'typeI familywise meets sample_size smallest_sample_size result binomial_result association_result matched_result rate_result two_stage_result confidence_interval difference_interval odds_ratio risk_ratio risk_difference prevalence_ratio prevalence_difference conditional_odds_ratio rate_ratio prevalence cumulative_incidence',
  data: 'observe responses observed_table observed_pairs observed_events',
})) for (const name of names.split(' ')) CALL_FAMILY[name] = family;
const familyOfCall = call => CALL_FAMILY[call] || 'analysis';
// Which blocks each step shapes, ringed in the preview while it is open.
const LIT = {
  kind: ['study', 'design'], outcome: ['study', 'null', 'analysis'], question: ['null', 'analysis'], test: ['analysis', 'study'],
  size: ['study', 'planning', 'data', 'value'], outcomes: ['study', 'analysis'], procedure: ['family', 'analysis'], looks: ['study', 'analysis'],
  aim: ['analysis', 'run'], rule: ['design', 'analysis'], stages: ['study', 'design', 'planning'], topic: ['study'], sampling: ['study'],
  analysis: ['analysis'], power: ['analysis', 'planning', 'data', 'value'], name: [],
};

function splitArgs(text) {
  const parts = [];
  let depth = 0;
  let inQuotes = false;
  let start = 0;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (c === '"') inQuotes = !inQuotes;
    else if (!inQuotes && (c === '(' || c === '[')) depth++;
    else if (!inQuotes && (c === ')' || c === ']')) depth--;
    else if (!inQuotes && !depth && c === ',') { parts.push(text.slice(start, i).trim()); start = i + 1; }
  }
  if (text.slice(start).trim()) parts.push(text.slice(start).trim());
  return parts;
}
// A `let` line as a palette-style block: the words of its calls and its inputs.
export function blocksOf(source) {
  const blocks = [];
  for (const line of source.split('\n')) {
    const found = /^let (\w+) = (.+)$/.exec(line);
    if (!found) continue;
    const [, name, expr] = found;
    const words = [];
    const inputs = [];
    const ref = value => /^[A-Za-z_]\w*$/.test(value);
    const walk = text => {
      const call = /^(\w+)\((.*)\)$/.exec(text);
      if (!call) { inputs.push({value: text, ref: ref(text)}); return; }
      words.push(call[1]);
      for (const arg of splitArgs(call[2])) {
        const pair = /^(\w+)=(.*)$/.exec(arg);
        const inner = pair && /^(\w+)\(/.exec(pair[2]);
        if (inner) inputs.push({key: pair[1], value: inner[1].replaceAll('_', ' '), call: familyOfCall(inner[1])});
        else if (pair) inputs.push({key: pair[1], value: pair[2], ref: ref(pair[2])});
        else walk(arg);
      }
    };
    const field = /^(\w+)\.[\w.]*?(\w+)$/.exec(expr);
    if (field) { words.push(field[2]); inputs.push({key: 'from', value: field[1], ref: true}); }
    else walk(expr);
    blocks.push({name, family: field ? 'value' : familyOfCall(words[0]), words: words.map(w => w.replaceAll('_', ' ')).join(' '), inputs});
  }
  return blocks;
}

// What each slot accepts on its own, to ring the wrong one red.
const count = text => /^\d+$/.test(String(text).trim());
const positive = text => fraction(text) && eval_(text) > 0;
const SLOT_FITS = {
  control: isWhole, treatment: isWhole, exposed: isWhole, unexposed: isWhole, cases: isWhole, controls: isWhole, total: isWhole,
  clustersControl: isWhole, clustersTreatment: isWhole, interimControl: isWhole, interimTreatment: isWhole, n: isWhole, n1: isWhole, n2: isWhole,
  visits: text => isWhole(text) && Number(text) >= 2, blockSize: text => isWhole(text) && Number(text) >= 2, clusters: isWhole, maxTotal: isWhole,
  rho: text => Number.isFinite(eval_(text)) && eval_(text) > -1 && eval_(text) < 1, slopeValue: text => Number.isFinite(eval_(text)),
  exposureSd: positive, residualSd: positive, deff: positive, outcomeSd: positive, moe: positive,
  cv: text => fraction(text) && eval_(text) >= 0 && eval_(text) <= 3,
  sdTreatment: text => !text.trim() || positive(text), skew: text => ratio(text) !== null && Math.abs(eval_(text)) <= 4,
  delay: text => fraction(text) && eval_(text) >= 0,
  skewY: text => ratio(text) !== null && Math.abs(eval_(text)) <= 4, skewX: text => ratio(text) !== null && Math.abs(eval_(text)) <= 4,
  interimN: text => isWhole(text) && Number(text) >= 2, maxN: isWhole,
  correlation: text => fraction(text) && eval_(text) >= 0 && eval_(text) < 1,
  assurance: text => !text.trim() || isShare(text),
  meanUnexposed: text => Number.isFinite(eval_(text)), meanExposed: text => Number.isFinite(eval_(text)),
  margin: positive, sd: positive, icc: text => fraction(text) && eval_(text) >= 0 && eval_(text) < 1, effect: text => Number.isFinite(eval_(text)), base: isShare, share: isShare, ratio: text => eval_(text) > 0 && eval_(text) !== 1,
  pControl: isShare, pTreatment: isShare, hazard: text => eval_(text) > 0 && eval_(text) !== 1, events: isWhole, nullRate: isShare, target: isShare,
  median: positive, accrual: text => fraction(text) && eval_(text) >= 0, followUp: text => fraction(text) && eval_(text) >= 0,
  continueAt: isShare, successAt: isShare, priorA: isWhole, priorB: isWhole, continueAbove: count, rejectAbove: count, count, controlSuccesses: count,
  treatmentSuccesses: count, exposedEvents: count, unexposedEvents: count, exposedTime: positive, unexposedTime: positive,
  exposure: studyName, named: studyName, name: text => /^[\w.-]+$/.test(text), method: text => text.trim().length > 0, endpoint: studyName,
  exposedCases: count, exposedNoncases: count, unexposedCases: count, unexposedNoncases: count,
  bothExposed: count, caseExposedOnly: count, controlExposedOnly: count, neitherExposed: count,
};
const fits = input => (SLOT_FITS[input.dataset.slot || input.dataset.key] || (() => true))(input.value.trim());

const DEFAULTS = {
  alpha: '1/20', alphaChosen: false, add: 'none',
  outcome: 'binary', control: 50, treatment: 50, question: 'differ', better: 'higher', margin: '1/10', unit: 'participants',
  clustersControl: 12, clustersTreatment: 12, visits: 3, test: undefined, scheme: 'complete', blockSize: 4, draws: 'every',
  method: 'Stratified Cochran-Mantel-Haenszel test', reference: '', effect: '5', sd: '10', icc: '1/20', pControl: '3/10', pTreatment: '1/2',
  rho: '1/5', slopeValue: '1/2', exposureSd: '4', residualSd: '15', deff: '2', cv: '0', sdTreatment: '', skew: '0', delay: '0', skewY: '0', skewX: '0', reestimate: 'fixed', interimN: 25, maxN: 150, severalAdd: 'none', rejecting: 'any', correlation: '1/2', meanUnexposed: '120', meanExposed: '125', outcomeSd: '15',
  hazard: '7/10', events: '60', median: '12', accrual: '24', followUp: '12', controlSuccesses: 12, treatmentSuccesses: 24,
  procedure: 'bonferroni', endpoints: [{name: 'response', kind: 'binary'}, {name: 'remission', kind: 'binary'}],
  interimControl: 25, interimTreatment: 25, spending: 'little',
  aim: 'test', n: 30, nullRate: '1/5', target: '2/5', count: 12, level: '19/20',
  rule: 'threshold', find: 'search', criterion: 'optimal', maxTotal: 45, n1: 13, n2: 30, continueAbove: 3, rejectAbove: 12,
  priorA: 1, priorB: 1, continueAt: '1/2', successAt: '19/20',
  design: 'cohort', exposure: 'smoking', named: 'asthma', exposed: 100, unexposed: 200, cases: 100, controls: 200, total: 400,
  population: false, outcomeScale: 'binary', exposureScale: 'binary', survey: 'simple_random', clusters: 100, covariates: 'age, sex',
  base: '1/10', ratio: '2', share: '3/10', exposedTime: '8000', unexposedTime: '24000', exposedEvents: 20, unexposedEvents: 30,
  table: null, pairs: null,
};
const LEVELS = {'1/20': {label: '5%', detail: '1/20'}, '1/40': {label: '2.5%', detail: '1/40'}, '1/100': {label: '1%', detail: '1/100'}};

// start: {design} opens on that design's first question; {family} on that family's cards.
// check(source) resolves to {errors}: the compiler's errors, so only a study that compiles is created.
export function openWizard({onCreate, onEmpty, check, start = {}}) {
  const back = el('div', 'wizard-back');
  const box = el('section', 'wizard');
  box.setAttribute('role', 'dialog');
  box.setAttribute('aria-modal', 'true');
  box.setAttribute('aria-label', 'New study');
  const first = designById(start.design) || DESIGNS[0];
  const state = {name: 'my-study', ...structuredClone(DEFAULTS), ...first.preset, designId: first.id,
    seed: 1 + Math.floor(Math.random() * 99999)};
  let tab = FAMILIES.some(f => f.id === start.family) ? start.family : first.family;
  let at = 'kind';
  const design = () => designById(state.designId);
  const flow = () => design().flow;
  const route = () => ROUTES[flow()];
  const made_ = () => FLOWS[flow()](flow() === 'observed' ? {...state, outcome: state.named} : state);
  const close = () => { back.remove(); document.removeEventListener('keydown', keys, true); clearTimeout(checkTimer); };
  const keys = event => {
    if (event.key !== 'Escape') return;
    event.preventDefault();
    event.stopPropagation();
    if (search.value && document.activeElement === search) { search.value = ''; paint(); } else close();
  };
  document.addEventListener('keydown', keys, true);
  back.addEventListener('pointerdown', event => { if (event.target === back) close(); });

  // Controls -----------------------------------------------------------------------
  const form = el('form', 'wizard-form');
  form.noValidate = true;
  // Radios are named per group; data-key says which answer they hold.
  const radio = (name, key, value, onPick) => {
    const input = el('input', 'wizard-radio');
    Object.assign(input, {type: 'radio', name, value});
    input.dataset.key = key;
    input.addEventListener('change', () => { if (input.checked) onPick(value); });
    return input;
  };
  const pick = key => value => { state[key] = value; paint(); };
  // Big tiles: a drawing, a label, one line of detail and, when it is known, the evidence.
  const tiles = (name, entries, onPick, {cls = '', key = name} = {}) => {
    const group = el('div', 'wizard-choices ' + cls);
    group.setAttribute('role', 'radiogroup');
    for (const [value, info] of Object.entries(entries)) {
      const option = el('label', 'wizard-choice');
      option.dataset.value = value;
      const words = el('span', 'wizard-choice-words');
      const title = el('strong', '', info.label);
      if (info.evidence) title.append(seal(info.evidence));
      words.append(title, el('span', '', info.example || info.detail || ''));
      const badge = el('span', 'wizard-glyph');
      badge.append(glyph(info.glyph || value));
      const tick = el('span', 'wizard-tick');
      tick.append(icon('check'));
      option.append(radio(name, key, value, onPick), badge, words, tick);
      group.append(option);
    }
    return group;
  };
  // A row of small pills for a choice of two to four.
  const segments = (name, entries, onPick, key = name) => {
    const group = el('div', 'wizard-segments');
    group.setAttribute('role', 'radiogroup');
    for (const [value, info] of Object.entries(entries)) {
      const option = el('label', 'wizard-segment');
      option.append(radio(name, key, value, onPick));
      if (info.glyph) option.append(glyph(info.glyph));
      option.append(el('strong', '', info.label));
      if (info.detail) option.append(el('span', '', info.detail));
      group.append(option);
    }
    return group;
  };
  // A white value slot, as on a block, that writes one answer.
  const pill = (key, {wide = false, numeric = false, label = '', onInput} = {}) => {
    const input = el('input', 'wizard-pill' + (wide ? ' wide' : ''));
    Object.assign(input, {value: key ? state[key] ?? '' : '', spellcheck: false, autocomplete: 'off'});
    if (key) input.dataset.key = key;
    if (numeric) input.inputMode = 'numeric';
    if (label) input.setAttribute('aria-label', label);
    input.addEventListener('input', () => { (onInput || (v => { state[key] = v; }))(input.value.trim()); paint(); });
    return input;
  };
  const sentence = (...parts) => {
    const line = el('p', 'wizard-sentence');
    line.append(...parts.map(item => typeof item === 'string' ? el('span', '', item) : item));
    return line;
  };
  const row = (label, control, hint) => {
    const line = el('label', 'wizard-row');
    line.append(el('span', 'wizard-row-label', label), control);
    if (hint) line.append(el('span', 'wizard-hint', hint));
    return line;
  };
  const rows = (...items) => { const node = el('div', 'wizard-rows'); node.append(...items); return node; };
  const note = text => el('p', 'wizard-note', text);
  const heading = text => el('span', 'wizard-label', text);
  const part = (...items) => { const node = el('div', 'wizard-part'); node.append(...items); return node; };
  // Rebuild a part only when what it shows changes, so typing keeps its focus.
  const swap = (node, key, build) => {
    if (node.dataset.swap === key) return;
    node.dataset.swap = key;
    node.replaceChildren(...build());
  };

  // Pages --------------------------------------------------------------------------
  const pages = {};
  for (const [key, info] of Object.entries(STEPS)) {
    const page = el('section', 'wizard-step');
    page.dataset.step = key;
    if (info.family) page.dataset.family = info.family;
    const hat = el('h2', 'wizard-hat');
    hat.append(el('span', 'wizard-hat-n'), el('span', 'wizard-hat-title', info.title));
    const panel = el('div', 'wizard-panel');
    page.append(hat, panel);
    pages[key] = {page, panel, hat};
  }
  const levelRow = part(heading('Level: the chance of a false positive'),
    segments('alpha', LEVELS, value => { state.alpha = value; state.alphaChosen = true; paint(); }));
  const levelSlot = () => el('div', 'wizard-level-slot');

  // Design: search, the five families, and the cards of one family or of the search.
  const search = el('input', 'wizard-search-input');
  Object.assign(search, {type: 'search', placeholder: 'Search designs: cluster, interim, survey, matched…', spellcheck: false, autocomplete: 'off'});
  search.setAttribute('aria-label', 'Search designs');
  search.addEventListener('input', () => paint());
  const searchBox = el('label', 'wizard-search');
  searchBox.append(glyph('search'), search);
  const familyTabs = el('div', 'wizard-families');
  familyTabs.setAttribute('role', 'tablist');
  familyTabs.setAttribute('aria-label', 'Families of designs');
  const tabButtons = FAMILIES.map(family => {
    const tabButton = button('', () => { tab = family.id; search.value = ''; paint(); }, 'wizard-family');
    tabButton.dataset.family = family.family;
    tabButton.dataset.id = family.id;
    tabButton.setAttribute('role', 'tab');
    tabButton.append(el('span', 'wizard-family-dot'), el('span', 'wizard-family-label', family.label));
    tabButton.title = family.title;
    familyTabs.append(tabButton);
    return tabButton;
  });
  // Arrow keys move between the families, as in any tab list.
  familyTabs.addEventListener('keydown', event => {
    const step = {ArrowRight: 1, ArrowLeft: -1}[event.key];
    if (!step) return;
    event.preventDefault();
    const i = FAMILIES.findIndex(f => f.id === tab);
    tab = FAMILIES[(i + step + FAMILIES.length) % FAMILIES.length].id;
    search.value = '';
    paint();
    tabButtons.find(b => b.dataset.id === tab).focus();
  });
  const familyNote = note('');
  // The cards' radios hold the chosen card, state.designId, not the observational design.
  const cards = tiles('design', Object.fromEntries(DESIGNS.map(d => [d.id, d])), id => choose(id), {cls: 'two wizard-designs', key: 'designId'});
  for (const card of cards.children) {
    const d = designById(card.dataset.value);
    card.dataset.group = d.family;
    card.dataset.family = FAMILIES.find(f => f.id === d.family).family;
    card.addEventListener('dblclick', () => go(1));
  }
  const nothing = note('');
  nothing.classList.add('wizard-empty');
  pages.kind.panel.append(searchBox, familyTabs, familyNote, cards, nothing);
  // A new card starts its flow afresh; picking the same card again keeps the answers.
  function choose(id) {
    if (id === state.designId) return paint();
    const {name, seed} = state;
    for (const key of Object.keys(state)) delete state[key];
    Object.assign(state, structuredClone(DEFAULTS), designById(id).preset, {name, seed, designId: id});
    for (const node of form.querySelectorAll('[data-swap]')) delete node.dataset.swap;
    for (const input of form.querySelectorAll('.wizard-pill[data-key]')) input.value = state[input.dataset.key] ?? '';
    paint();
  }

  // Trial: outcome, question, randomisation and test, size.
  const visitsBox = part(sentence('Measured at', pill('visits', {numeric: true, label: 'Visits'}), 'visits'));
  const outcomeTiles = tiles('outcome', OUTCOMES, pick('outcome'));
  pages.outcome.panel.append(outcomeTiles, visitsBox);
  const betterBox = el('div', 'wizard-part');
  const questionBox = el('div', 'wizard-part');
  const whyNote = note('');
  const marginRow = row('Margin', pill('margin', {label: 'Margin'}), 'In the outcome\'s units; for yes or no, a difference in proportions.');
  pages.question.panel.append(betterBox, questionBox, whyNote, marginRow);
  const unitBox = part(heading('Who is randomised?'), segments('unit', {
    participants: {label: 'Participants', glyph: 'participants'}, clusters: {label: 'Whole clusters', detail: 'clinics, schools', glyph: 'clusters'}}, pick('unit')));
  const testBox = el('div', 'wizard-part');
  const blocksLine = sentence('Blocks of', pill('blockSize', {numeric: true, label: 'Block size'}), 'units');
  const schemeBox = part(heading('How was it randomised?'), segments('scheme', {
    complete: {label: 'Completely'}, stratified: {label: 'In 2 strata'}, blocked: {label: 'In blocks'}}, pick('scheme')),
  blocksLine, segments('draws', {every: {label: 'Count every split'}, draws: {label: 'Draw 9,999 splits', detail: 'Monte Carlo'}}, pick('draws')));
  const declaredBox = rows(row('Method', pill('method', {wide: true, label: 'Method'}), 'What the test is.'),
    row('Reference', pill('reference', {wide: true, label: 'Reference'}), 'Optional: where it is specified.'));
  pages.test.panel.append(unitBox, testBox, schemeBox, declaredBox);
  const trialSizes = el('div', 'wizard-part');
  const trialAlso = el('div', 'wizard-part');
  const trialPlan = el('div', 'wizard-rows');
  const trialData = el('div', 'wizard-part');
  const trialSize = part(trialSizes, levelSlot(), trialAlso, trialPlan, trialData);

  // Several outcomes: their names and kinds, and how the level is shared.
  const endpointRows = el('div', 'wizard-endpoints');
  const addEndpoint = button('', () => {
    if (state.endpoints.length >= 4) return;
    const names = ['response', 'remission', 'relapse', 'quality of life', 'outcome'];
    state.endpoints.push({name: names.find(n => !state.endpoints.some(e => e.name === n)), kind: 'binary'});
    paint();
  }, 'btn ghost small wizard-add');
  addEndpoint.append(icon('plus'), 'Add an outcome');
  pages.outcomes.panel.append(endpointRows, addEndpoint, note('All are measured on the same participants, so they share one assignment.'));
  const procedureNote = note('');
  pages.procedure.panel.append(tiles('procedure', Object.fromEntries(Object.entries(PROCEDURES).map(([k, v]) =>
    [k, {...v, evidence: k === 'graphical' ? 'cited' : k === 'fixed_sequence' ? 'conditional' : undefined}])), pick('procedure')), procedureNote);
  const severalSize = part(sentence(pill('control', {numeric: true, label: 'Control'}), 'in control and', pill('treatment', {numeric: true, label: 'Treatment'}), 'in treatment'), levelSlot());
  // The family's power, simulated with its own procedure.
  const severalPower = el('div', 'wizard-part');
  pages.procedure.panel.append(severalPower);

  // Interim look: the sizes at the look and at the end, and how the level is spent.
  pages.looks.panel.append(
    sentence('Look at', pill('interimControl', {numeric: true, label: 'Control at the look'}), 'and', pill('interimTreatment', {numeric: true, label: 'Treatment at the look'}), 'participants'),
    sentence('End at', pill('control', {numeric: true, label: 'Control at the end'}), 'and', pill('treatment', {numeric: true, label: 'Treatment at the end'}), 'participants'),
    part(heading('How is the level spent?'), segments('spending', SPENDING, pick('spending'))), levelSlot());
  // A measured outcome's looks are t-tests, whose power can be simulated look by look.
  const interimPower = el('div', 'wizard-part');
  pages.looks.panel.append(interimPower);
  function paintInterim() {
    // Fisher's looks are summed exactly; t-test looks are simulated; log-rank looks are not planned.
    const kind = state.outcome === 'continuous' ? 'measured' : state.outcome === 'binary' ? 'binary' : null;
    if (!kind) state.interimAdd = 'none';
    swap(interimPower, String(kind) + (state.interimAdd || 'none'), () => !kind ? [] : [
      heading('Also'),
      segments('interim-add', {none: {label: 'Nothing more', glyph: 'none'}, power: {label: 'Find the power', glyph: 'target'}},
        value => { state.interimAdd = value; paint(); }, 'interimAdd'),
      ...(state.interimAdd !== 'power' ? [] : kind === 'binary' ? [rows(
        row('Control rate', pill('pControl', {label: 'Control response rate'}), 'The response rate you expect without treatment.'),
        row('Treatment rate', pill('pTreatment', {label: 'Treatment response rate'}), 'And with it.')),
      note('Power, the chance of stopping at the look and the expected size are summed exactly.')] : [rows(
        row('Expected difference', pill('effect', {label: 'Expected difference'}), 'Treatment minus control.'),
        row('Standard deviation', pill('sd', {label: 'Standard deviation'}), 'Of one participant\'s outcome.')),
      note('Power, the chance of stopping at the look and the expected size are simulated.')])]);
  }

  // One group: what is asked, and the numbers.
  pages.aim.panel.append(tiles('aim', AIMS, pick('aim')));
  const oneArmTest = rows(row('Participants', pill('n', {numeric: true, label: 'Participants'})),
    row('Benchmark rate', pill('nullRate', {label: 'Benchmark rate'}), 'The rate to beat, such as 1/5.'),
    row('Hoped-for rate', pill('target', {label: 'Hoped-for rate'}), '80% power is checked here.'));
  const oneArmEstimate = part(sentence(pill('count', {numeric: true, label: 'Responses'}), 'responded, of', pill('n', {numeric: true, label: 'Participants'})),
    part(heading('Confidence'), segments('level', {'19/20': {label: '95%'}, '9/10': {label: '90%'}, '99/100': {label: '99%'}}, pick('level'))));
  const oneArmLevel = levelSlot();
  const oneArmAlso = el('div', 'wizard-part');
  const oneArmCount = part(sentence(pill('count', {numeric: true, label: 'Responses'}), 'responded'));
  const oneArmPrecision = el('div', 'wizard-part');
  const oneArmSize = part(oneArmTest, oneArmEstimate, oneArmLevel, oneArmAlso, oneArmCount, oneArmPrecision);
  pages.size.panel.append(trialSize, severalSize, oneArmSize);

  // Two stages: the rule, then a design found or given.
  pages.rule.panel.append(tiles('rule', RULES, pick('rule')));
  const findBox = part(segments('find', {search: {label: 'Find the best design', glyph: 'search'}, given: {label: 'I have a design', glyph: 'pencil'}}, pick('find')));
  const searchRows = part(segments('criterion', {optimal: {label: 'Optimal', detail: 'smallest expected size'}, minimax: {label: 'Minimax', detail: 'smallest largest size'}}, pick('criterion')),
    rows(row('Up to', pill('maxTotal', {numeric: true, label: 'Largest total'}), 'participants in all.')));
  const givenRows = rows(row('Stage one', pill('n1', {numeric: true, label: 'Stage one'}), 'participants.'), row('Stage two', pill('n2', {numeric: true, label: 'Stage two'}), 'participants.'));
  const thresholdRows = rows(row('Continue above', pill('continueAbove', {numeric: true, label: 'Continue above'}), 'responses in stage one.'),
    row('Reject above', pill('rejectAbove', {numeric: true, label: 'Reject above'}), 'responses in all.'));
  const posteriorRows = rows(row('Beta prior', sentence(pill('priorA', {numeric: true, label: 'Prior a'}), pill('priorB', {numeric: true, label: 'Prior b'}))),
    row('Continue at', pill('continueAt', {label: 'Continue at'}), 'posterior probability above the benchmark.'),
    row('Succeed at', pill('successAt', {label: 'Succeed at'}), 'posterior probability at the end.'));
  const rateRows = rows(row('Benchmark rate', pill('nullRate', {label: 'Benchmark rate'})), row('Hoped-for rate', pill('target', {label: 'Hoped-for rate'})));
  pages.stages.panel.append(findBox, searchRows, givenRows, thresholdRows, posteriorRows, rateRows, levelSlot());

  // Observational: topic, sampling, test, then the level and what else to add.
  const scalesBox = el('div', 'wizard-part');
  pages.topic.panel.append(
    sentence('Are', pill('exposure', {wide: true, label: 'Exposure'}), 'and', pill('named', {wide: true, label: 'Outcome'}), 'associated?'),
    scalesBox, note('Name the exposure and the outcome in a few plain words. A test speaks of association, not of an effect of the exposure.'));
  const populationBox = part(segments('population', {
    groups: {label: 'Two groups', detail: 'exposed and unexposed, recruited', glyph: 'groups'},
    population: {label: 'One population', detail: 'sampled, exposure measured', glyph: 'population'}},
  value => { state.population = value === 'population'; paint(); }));
  populationBox.dataset.part = 'population';
  const surveyBox = part(heading('How was the sample drawn?'), segments('survey', SURVEYS, pick('survey')));
  const surveyClusters = sentence(pill('clusters', {numeric: true, label: 'Sampled clusters'}), 'clusters sampled');
  const groupSizes = el('div', 'wizard-part');
  pages.sampling.panel.append(populationBox, surveyBox, surveyClusters, groupSizes);
  const observedTestBox = el('div', 'wizard-part');
  const covariatesRow = row('Adjusted for', pill('covariates', {wide: true, label: 'Covariates'}), 'Covariates, separated by commas.');
  pages.analysis.panel.append(observedTestBox, covariatesRow);
  const observedAlso = el('div', 'wizard-part');
  const observedPlan = el('div', 'wizard-rows');
  const observedData = el('div', 'wizard-part');
  const observedPrecision = el('div', 'wizard-part');
  pages.power.panel.append(levelSlot(), observedAlso, observedPlan, observedPrecision, observedData);
  // A margin of error, absolute or relative, and an assurance if wanted: the same for every flow.
  const choosePrecision = value => {
    state.precisionMeasure = value;
    Object.assign(state, marginDefaults(value));
    for (const input of form.querySelectorAll('.wizard-pill[data-key="moe"]')) input.value = state.moe;
    paint();
  };
  const marginRows = () => [
    part(heading('Margin of error'), segments('margin-kind', MARGIN_KINDS, pick('marginKind'), 'marginKind')),
    rows(row('Margin', pill('moe', {label: 'Margin of error'}), state.marginKind === 'relative' ?
      'A fraction of the planning value, such as 1/5; for a ratio, the lower limit at least (1 - r) times the estimate.' :
      'Half the interval\'s width, such as 3/100 for 3 percentage points.'),
    row('Assurance', pill('assurance', {label: 'Assurance'}), 'The chance the interval is that narrow, such as 4/5; leave blank for the interval at the expected counts.'))];

  // Name.
  const name = pill('name', {wide: true, label: 'File name', onInput: v => { state.name = v || 'my-study'; }});
  const verdict = el('div', 'wizard-verdict');
  const preview = el('pre', 'wizard-preview');
  const code = el('details', 'wizard-code');
  code.append(el('summary', '', 'Show the code'), preview);
  pages.name.panel.append(sentence(name, el('span', 'wizard-ext', '.stat')), verdict, code);

  // Frame ----------------------------------------------------------------------------
  const head = el('header', 'wizard-head');
  const titles = el('div', 'wizard-titles');
  const countText = el('span', 'wizard-count');
  titles.append(el('strong', '', 'New study'), countText);
  const shut = button('', close, 'icon-btn wizard-close');
  shut.append(icon('x'));
  shut.setAttribute('aria-label', 'Close');
  const trail = el('nav', 'wizard-trail');
  trail.setAttribute('aria-label', 'Steps');
  head.append(titles, shut, trail);
  const steps = el('div', 'wizard-steps');
  steps.append(...Object.values(pages).map(p => p.page));
  const side = el('aside', 'wizard-blocks');
  side.setAttribute('aria-label', 'The blocks this study will have');
  const stack = el('div', 'wizard-stack');
  const grade = el('p', 'wizard-grade');
  side.append(el('span', 'wizard-label', 'Your blocks'), stack, grade, el('p', 'wizard-note', 'Every block can be changed afterwards.'));
  const main = el('div', 'wizard-main');
  main.append(steps, side);
  const problem = el('p', 'wizard-problem');
  problem.setAttribute('role', 'status');
  const empty = button('Start empty', () => { close(); onEmpty(); }, 'btn ghost');
  const previous = button('Back', () => go(-1), 'btn ghost');
  const next = button('Next', null, 'btn primary');
  next.type = 'submit';
  const foot = el('footer', 'wizard-foot');
  foot.append(empty, problem, previous, next);
  form.append(head, main, foot);

  const go = delta => {
    const r = route();
    show(r[Math.max(0, Math.min(r.length - 1, r.indexOf(at) + delta))], delta >= 0 ? 'forward' : 'back');
  };
  function show(step, way = 'forward') {
    if (step === at) return;
    at = step;
    paint();
    const page = pages[step].page;
    page.classList.remove('forward', 'back');
    void page.offsetWidth;
    page.classList.add(way);
    const target = step === 'kind' ? search :
      [...page.querySelectorAll('.wizard-radio:checked, input:not([type="radio"])')].find(input => !input.closest('[hidden]'));
    target?.focus({preventScroll: true});
    // Bring the blocks this step shapes into view.
    const lit = stack.querySelector('.wiz-block.lit');
    if (lit && (lit.offsetTop < side.scrollTop || lit.offsetTop + lit.offsetHeight > side.scrollTop + side.clientHeight)) {
      side.scrollTo?.({top: lit.offsetTop - 44, behavior: 'smooth'});
    } else if (!lit) side.scrollTo?.({top: 0, behavior: 'smooth'});
  }
  form.addEventListener('submit', async event => {
    event.preventDefault();
    if (at === 'kind') {
      // Enter in the search box takes the first design it found.
      const visible = [...cards.children].filter(card => !card.hidden);
      if (search.value && visible.length && !visible.some(card => card.dataset.value === state.designId)) choose(visible[0].dataset.value);
    }
    if (at !== route().at(-1)) { if (!next.disabled) go(1); return; }
    if (Object.keys(problems()).length) return;
    const source = made_().source;
    next.disabled = true;
    const errors = await compiled(source);
    if (errors.length || !back.isConnected) { paint(); return; }
    close();
    onCreate(state.name.replace(/\.stat$/, '') + '.stat', source);
  });

  // The compiler has the last word: a study is created only when it compiles.
  const checks = new Map();
  let checkTimer = null;
  function compiled(source) {
    if (!check) return Promise.resolve([]);
    if (!checks.has(source)) {
      checks.set(source, Promise.resolve().then(() => check(source)).then(r => r?.errors || []).catch(() => []).then(errors => {
        checks.set(source, errors);
        if (back.isConnected && made_().source === source) paint();
        return errors;
      }));
    }
    const known = checks.get(source);
    return Array.isArray(known) ? Promise.resolve(known) : known;
  }
  const checkLater = source => {
    clearTimeout(checkTimer);
    if (check && !checks.has(source)) checkTimer = setTimeout(() => compiled(source), 250);
  };

  // What is wrong, step by step.
  function problems() {
    const found = {};
    const say = (step, ok, text) => { if (!ok && !found[step]) found[step] = text; };
    const whole = keys => keys.every(key => isWhole(state[key]));
    say('name', /^[\w.-]+$/.test(state.name), 'Use letters, digits, dots, dashes or underscores in the name.');
    const f = flow();
    if (f === 'trial') {
      say('outcome', state.outcome !== 'repeated' || SLOT_FITS.visits(String(state.visits)), 'Give at least 2 visits.');
      say('question', state.question !== 'margin' || positive(state.margin), 'The margin must be a positive number, such as 1/10 or 0.1.');
      const test = trialTest(state);
      say('test', test !== 'declared_test' || String(state.method).trim(), 'Say what the test is.');
      say('test', test !== 'randomisation_test' || state.scheme !== 'blocked' || SLOT_FITS.blockSize(String(state.blockSize)), 'Blocks need at least 2 units.');
      say('size', whole(['control', 'treatment']), 'Each arm needs a whole number of participants.');
      say('size', state.unit !== 'clusters' || whole(['clustersControl', 'clustersTreatment']), 'Each arm needs a whole number of clusters.');
      const extras = trialExtras(state);
      if (state.add === 'plan' && extras.plan) {
        if (state.outcome === 'binary') say('size', !ratesPlannable(state), ratesPlannable(state));
        else if (extras.plan === 'survival') {
          say('size', SLOT_FITS.hazard(state.hazard), 'The hazard ratio must be a positive number other than 1, such as 7/10.');
          say('size', SLOT_FITS.median(state.median), 'The control median must be a positive time, such as 12.');
          say('size', SLOT_FITS.accrual(state.accrual) && SLOT_FITS.followUp(state.followUp) && eval_(state.accrual) + eval_(state.followUp) > 0,
            'Accrual and follow-up are times of at least 0, and not both 0.');
        } else {
          say('size', positive(state.sd), 'The standard deviation must be a positive number, such as 10.');
          say('size', !plannable(state), plannable(state));
        }
      }
      if (state.add === 'data' && extras.data) {
        say('size', count(state.controlSuccesses) && count(state.treatmentSuccesses), 'Responders are whole numbers.');
        say('size', Number(state.controlSuccesses) <= Number(state.control) && Number(state.treatmentSuccesses) <= Number(state.treatment), 'Responders cannot outnumber an arm.');
      }
    } else if (f === 'several') {
      const names = state.endpoints.map(e => e.name);
      say('outcomes', names.every(studyName), 'Name each outcome in a few plain words, starting with a letter.');
      say('outcomes', new Set(names.map(n => n.toLowerCase())).size === names.length, 'Each outcome needs its own name.');
      say('size', whole(['control', 'treatment']), 'Each arm needs a whole number of participants.');
    } else if (f === 'interim') {
      say('looks', whole(['control', 'treatment', 'interimControl', 'interimTreatment']), 'Each size must be a whole number of participants.');
      say('looks', Number(state.interimControl) < Number(state.control) && Number(state.interimTreatment) < Number(state.treatment), 'The look comes before the end: fewer participants at the look.');
    } else if (f === 'one_arm') {
      say('size', isWhole(state.n) && Number(state.n) <= 1000, 'Give a whole number of participants, up to 1000.');
      if (state.aim === 'test') {
        say('size', isShare(state.nullRate) && isShare(state.target), 'Each rate must lie between 0 and 1, such as 1/5.');
        say('size', eval_(state.target) > eval_(state.nullRate), 'The hoped-for rate must be above the benchmark.');
      }
      if (state.aim === 'estimate' || state.add === 'data') say('size', count(state.count) && Number(state.count) <= Number(state.n), 'Responses are a whole number, at most the participants.');
      if (state.aim === 'estimate' && state.add === 'precision') {
        say('size', isShare(state.base ?? state.target), 'The expected rate must lie between 0 and 1, such as 3/10.');
        say('size', !precisionPlannable(state), precisionPlannable(state));
      }
    } else if (f === 'two_stage') {
      say('stages', isShare(state.nullRate) && isShare(state.target) && eval_(state.target) > eval_(state.nullRate), 'The hoped-for rate must lie above the benchmark, both between 0 and 1.');
      if (state.rule === 'threshold' && state.find === 'search') say('stages', isWhole(state.maxTotal) && Number(state.maxTotal) <= 120, 'Search up to 120 participants in all.');
      else {
        say('stages', isWhole(state.n1) && isWhole(state.n2) && Number(state.n1) <= 200 && Number(state.n2) <= 200, 'Each stage needs 1 to 200 participants.');
        if (state.rule === 'threshold') say('stages', count(state.continueAbove) && count(state.rejectAbove), 'Thresholds are whole numbers.');
        else say('stages', isWhole(state.priorA) && isWhole(state.priorB) && isShare(state.continueAt) && isShare(state.successAt), 'The prior takes whole numbers; the thresholds lie between 0 and 1.');
      }
    } else if (f === 'observed') {
      say('topic', studyName(state.exposure) && studyName(state.named), 'Name the exposure and the outcome in a few plain words, starting with a letter.');
      const fixedTotal = state.design === 'cross_sectional' || (state.design === 'cohort' && state.population);
      const sizes = {matched_case_control: ['cases'], case_control: ['cases', 'controls'], person_time: []}[state.design] || (fixedTotal ? ['total'] : ['exposed', 'unexposed']);
      say('sampling', whole(sizes), 'Each size must be a whole number of participants.');
      say('sampling', state.design !== 'cross_sectional' || state.survey !== 'cluster' || isWhole(state.clusters), 'Give the number of clusters sampled.');
      const extras = observedExtras(state);
      if (state.add === 'plan' && extras.plan) say('power', !observationalPlannable(state), observationalPlannable(state));
      if (state.add === 'data' && extras.data) say('power', [...observedData.querySelectorAll('.wizard-pill')].every(fits), 'Each count must be a whole number.');
      if (state.add === 'precision' && extras.precision) {
        say('power', [...observedPrecision.querySelectorAll('.wizard-pill')].every(fits), 'Each value must be a number, such as 1/10.');
        say('power', !precisionPlannable({...state, precisionMeasure: precisionMeasure(state)}), precisionPlannable({...state, precisionMeasure: precisionMeasure(state)}));
      }
    }
    return found;
  }

  // Painting -----------------------------------------------------------------------------
  const familyOf = id => FAMILIES.find(f => f.id === id)?.family || 'study';
  function paint() {
    const f = flow();
    const r = route();
    if (!r.includes(at)) at = 'kind';
    const index = r.indexOf(at);
    for (const [key, {page, hat}] of Object.entries(pages)) {
      page.hidden = key !== at;
      hat.firstChild.textContent = r.includes(key) ? String(r.indexOf(key) + 1) : '';
      hat.lastChild.textContent = TITLES[f]?.[key] || STEPS[key].title;
    }
    countText.textContent = 'Step ' + (index + 1) + ' of ' + r.length + ' · ' + design().label;
    paintKind();
    for (const tile of outcomeTiles.children) tile.hidden = f === 'interim' && tile.dataset.value === 'repeated';
    if (f === 'trial') paintTrial();
    if (f === 'several') paintSeveral();
    if (f === 'one_arm') paintOneArm();
    if (f === 'two_stage') paintTwoStage();
    if (f === 'observed') paintObserved();
    if (f === 'interim') paintInterim();
    visitsBox.hidden = f !== 'trial' || state.outcome !== 'repeated';
    trialSize.hidden = f !== 'trial';
    severalSize.hidden = f !== 'several';
    oneArmSize.hidden = f !== 'one_arm';
    // The level moves to whichever page is showing and asks for it.
    const slot = [...pages[at].panel.querySelectorAll('.wizard-level-slot')].find(s => !s.closest('[hidden]'));
    if (slot && levelRow.parentNode !== slot) slot.append(levelRow);

    // Every choice shows the answer it holds.
    for (const input of form.querySelectorAll('.wizard-radio')) {
      const key = input.dataset.key;
      const value = key === 'population' ? (state.population ? 'population' : 'groups') :
        key.startsWith('endpoint:') ? state.endpoints[Number(key.slice(9))]?.kind : String(state[key]);
      input.checked = input.value === value;
    }

    const made = made_();
    preview.textContent = made.source;
    paintBlocks(made.source);
    paintVerdict(made);
    checkLater(made.source);

    // The trail, the problem of this step, and the buttons.
    const found = problems();
    const known = checks.get(made.source);
    const errors = Array.isArray(known) ? known : [];
    trail.replaceChildren(...r.map((key, i) => {
      const crumb = button('', () => show(key, i >= index ? 'forward' : 'back'), 'wizard-crumb');
      crumb.dataset.family = key === 'kind' ? familyOf(design().family) : STEPS[key].family;
      crumb.dataset.state = i === index ? 'current' : i < index ? 'done' : 'todo';
      if (found[key]) crumb.dataset.problem = '';
      if (i === index) crumb.setAttribute('aria-current', 'step');
      const mark = el('span', 'wizard-crumb-n');
      if (i < index && !found[key]) mark.append(icon('check')); else mark.textContent = String(i + 1);
      crumb.append(mark, el('span', 'wizard-crumb-label', STEPS[key].label));
      return crumb;
    }));
    for (const input of pages[at].panel.querySelectorAll('.wizard-pill')) {
      const wrong = Boolean(found[at]) && input.value.trim() !== '' && !fits(input);
      if (wrong) input.setAttribute('aria-invalid', 'true'); else input.removeAttribute('aria-invalid');
    }
    const last = at === r.at(-1);
    const firstProblem = r.find(key => found[key]);
    const local = found[at] || (last && firstProblem ? found[firstProblem] + ' (' + STEPS[firstProblem].label + ')' : '');
    problem.textContent = local || (errors.length ? 'StatClaim cannot build this yet: ' + errors[0] : '');
    problem.dataset.tone = local ? 'error' : errors.length ? 'compile' : '';
    previous.hidden = index === 0;
    next.textContent = last ? 'Create study' : 'Next';
    next.disabled = last ? Boolean(firstProblem) || errors.length > 0 : Boolean(found[at]);
  }

  function paintKind() {
    const words = search.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
    const searching = words.length > 0;
    let shown = 0;
    for (const card of cards.children) {
      const d = designById(card.dataset.value);
      const family = FAMILIES.find(x => x.id === d.family);
      const text = (d.label + ' ' + d.detail + ' ' + d.words + ' ' + family.title).toLowerCase();
      card.hidden = searching ? !words.every(word => text.includes(word)) : d.family !== tab;
      card.classList.toggle('searched', searching);
      if (!card.hidden) shown++;
    }
    for (const tabButton of tabButtons) {
      const on = !searching && tabButton.dataset.id === tab;
      tabButton.setAttribute('aria-selected', String(on));
      tabButton.tabIndex = on ? 0 : -1;
    }
    familyTabs.classList.toggle('searching', searching);
    const family = FAMILIES.find(x => x.id === tab);
    const designs = DESIGNS.filter(d => d.family === tab).length;
    familyNote.textContent = searching ? (shown ? shown + ' of ' + DESIGNS.length + ' designs' : '') : designs + ' designs · ' + family.detail;
    nothing.textContent = searching && !shown ? 'No design matches. Try cluster, interim, survey, matched or Bayesian.' : '';
    nothing.hidden = !nothing.textContent;
    pages.kind.page.dataset.family = searching ? familyOf(design().family) : family.family;
  }

  function paintTrial() {
    const allowed = available(state.outcome, state.better);
    if (!allowed[state.question]) state.question = 'differ';
    const yes = state.outcome === 'binary';
    swap(betterBox, state.outcome, () => state.outcome === 'survival' ? [] : [heading('Which way is better for patients?'), segments('better', {
      higher: {label: 'Higher', detail: yes ? 'more yeses' : 'a larger value', glyph: 'higher'},
      lower: {label: 'Lower', detail: yes ? 'fewer yeses' : 'a smaller value', glyph: 'lower'}}, pick('better'))]);
    const offered = Object.fromEntries(Object.entries(QUESTIONS).filter(([key]) => allowed[key]));
    swap(questionBox, Object.keys(offered).join(), () => [tiles('question', offered, value => {
      state.question = value;
      if (!state.alphaChosen) state.alpha = value === 'differ' ? '1/20' : '1/40';
      paint();
    })]);
    whyNote.textContent = allowed.why || '';
    whyNote.hidden = !allowed.why;
    marginRow.hidden = state.question !== 'margin';
    // The tests that answer this question for this outcome and assignment, proved first.
    const tests = trialTests(state);
    state.test = trialTest(state);
    swap(testBox, tests.join(), () => {
      const entries = Object.fromEntries(tests.map(id => [id, {...TRIAL_TESTS[id], glyph: {randomisation_test: 'dice', declared_test: 'pencil', logistic_regression: 'adjust', cluster_t_test: 'clusters'}[id] || 'differ'}]));
      const alone = tests.length === 1 && tests[0] === 'declared_test';
      return [heading('Which test?'), tiles('test', entries, pick('test')),
        ...(alone ? [note('StatClaim has no test for this question with this assignment: declare yours.')] : [])];
    });
    schemeBox.hidden = state.test !== 'randomisation_test';
    blocksLine.hidden = state.scheme !== 'blocked';
    declaredBox.hidden = state.test !== 'declared_test';
    const clusters = state.unit === 'clusters';
    swap(trialSizes, state.unit, () => clusters ? [
      sentence(pill('clustersControl', {numeric: true, label: 'Clusters in control'}), 'clusters with', pill('control', {numeric: true, label: 'Participants in control'}), 'participants in control'),
      sentence(pill('clustersTreatment', {numeric: true, label: 'Clusters in treatment'}), 'clusters with', pill('treatment', {numeric: true, label: 'Participants in treatment'}), 'participants in treatment')] : [
      sentence(pill('control', {numeric: true, label: 'Control'}), 'in control and', pill('treatment', {numeric: true, label: 'Treatment'}), 'in treatment')]);
    const extras = trialExtras(state);
    const options = {none: {label: 'Nothing more', glyph: 'none'}};
    if (extras.plan) options.plan = {label: 'Find the sample size', glyph: 'target'};
    if (extras.data) options.data = {label: 'Analyse results', glyph: 'table'};
    if (!options[state.add]) state.add = 'none';
    swap(trialAlso, Object.keys(options).join() + extras.plan, () => [heading('Also'), segments('add-trial', options, pick('add'), 'add')]);
    const plan = state.add === 'plan' ? extras.plan : null;
    trialPlan.hidden = !plan;
    // A cluster trial is planned with the intracluster correlation as well.
    const iccRow = plan === 'clusters' ? [row('Intracluster correlation', pill('icc', {label: 'Intracluster correlation'}),
      'How alike participants in one cluster are, from 0 to below 1, such as 1/20.'),
    row('Cluster size variation', pill('cv', {label: 'Coefficient of variation of cluster sizes'}),
      'Their SD over their mean, such as 1/2; 0 for equal clusters. Above 0, power is simulated.')] : [];
    // A simulated t-test can be planned in another scenario: unequal SDs or a skewed outcome.
    // A t-test's size can be re-estimated at an interim look instead of fixed in advance.
    const reestimateRows = plan === 'simulated' && state.test === 't_test' ? [part(heading('Size'),
      segments('reestimate', {fixed: {label: 'Fixed in advance'}, blinded: {label: 'Re-estimated at an interim look'}},
        value => { state.reestimate = value; paint(); }, 'reestimate')),
    ...(state.reestimate === 'blinded' ? [row('Interim look', pill('interimN', {numeric: true, label: 'Participants per arm at the interim look'}),
      'Per arm, before the planned size. The SD is estimated there, without unblinding.'),
    row('Largest size', pill('maxN', {numeric: true, label: 'Largest size per arm'}), 'Per arm; the size never goes above it.')] : [])] : [];
    const scenarioRows = plan === 'simulated' && state.reestimate !== 'blinded' ? [row('Treatment SD', pill('sdTreatment', {label: 'Treatment arm standard deviation'}),
      'Leave blank for the same SD in both arms; the SD above is then the control arm\'s.'),
    row('Skewness', pill('skew', {label: 'Skewness of the outcome'}), 'From -4 to 4; 0 for a normal outcome. Lengths of stay are often near 2.')] : [];
    swap(trialPlan, String(plan) + state.outcome + state.test + (state.reestimate || 'fixed'), () => !plan ? [] : state.outcome === 'binary' ? [
      row('Control rate', pill('pControl', {label: 'Control response rate'}), 'The response rate you expect without treatment.'),
      row('Treatment rate', pill('pTreatment', {label: 'Treatment response rate'}), 'And with it.'), ...iccRow] : plan === 'survival' ? [
      row('Hazard ratio', pill('hazard', {label: 'Hazard ratio'}), 'Treatment over control, such as 7/10.'),
      row('Control median', pill('median', {label: 'Control median'}), 'Time until half the control patients have the event.'),
      row('Accrual', pill('accrual', {label: 'Accrual period'}), 'How long patients enter, in the same unit.'),
      row('Follow-up', pill('followUp', {label: 'Follow-up'}), 'How long they are followed after the last one enters.'),
      row('Effect delay', pill('delay', {label: 'Effect delay'}), 'If the treatment acts only after a while, how long after entry; 0 if from the start. Above 0, power is simulated.')] : [
      row('Expected difference', pill('effect', {label: 'Expected difference'}), 'Treatment minus control.'),
      row('Standard deviation', pill('sd', {label: 'Standard deviation'}), state.outcome === 'repeated' ? 'Effective, for the contrast.' : 'Of one participant\'s outcome.'),
      ...iccRow, ...reestimateRows, ...scenarioRows]);
    trialData.hidden = state.add !== 'data';
    swap(trialData, state.add, () => state.add !== 'data' ? [] : [sentence(pill('controlSuccesses', {numeric: true, label: 'Responders in control'}), 'responded in control and',
      pill('treatmentSuccesses', {numeric: true, label: 'Responders in treatment'}), 'in treatment')]);
  }

  function paintSeveral() {
    swap(endpointRows, String(state.endpoints.length), () => state.endpoints.map((endpoint, i) => {
      const line = el('div', 'wizard-endpoint');
      const input = pill('', {wide: true, label: 'Outcome ' + (i + 1), onInput: v => { state.endpoints[i].name = v; }});
      input.value = endpoint.name;
      input.dataset.slot = 'endpoint';
      const remove = button('', () => { state.endpoints.splice(i, 1); paint(); }, 'icon-btn wizard-remove');
      remove.append(icon('x'));
      remove.setAttribute('aria-label', 'Remove this outcome');
      remove.hidden = state.endpoints.length <= 2;
      line.append(el('span', 'wizard-endpoint-n', String(i + 1)), input,
        segments('kind-' + i, {binary: {label: 'Yes or no'}, continuous: {label: 'Measured'}}, value => { state.endpoints[i].kind = value; paint(); }, 'endpoint:' + i), remove);
      return line;
    }));
    addEndpoint.hidden = state.endpoints.length >= 4;
    const k = state.endpoints.length;
    procedureNote.textContent = {
      bonferroni: 'Each of the ' + k + ' tests runs at ' + times(state.alpha, 1, k) + '. ' + (state.endpoints.every(e => e.kind === 'binary') ?
        'With yes-or-no outcomes, Lean proves the whole family.' : 'Lean checks the split; the t-tests\' own bounds are cited.'),
      fixed_sequence: 'Each test runs at the full ' + state.alpha + ', in the listed order, and only after every earlier one rejected.',
      graphical: 'Each starts with 1/' + k + ' of the level and passes it on equally after a rejection. The procedure\'s guarantee is cited.',
    }[state.procedure];
    const kinds = new Set(state.endpoints.map(e => e.kind));
    swap(severalPower, (state.severalAdd || 'none') + [...kinds].join(), () => [
      heading('Also'),
      segments('several-add', {none: {label: 'Nothing more', glyph: 'none'}, power: {label: 'Find the power', glyph: 'target'}},
        value => { state.severalAdd = value; paint(); }, 'severalAdd'),
      ...(state.severalAdd === 'power' ? [
        segments('rejecting', {any: {label: 'Reject at least one'}, all: {label: 'Reject every one'}}, value => { state.rejecting = value; paint(); }, 'rejecting'),
        rows(
          ...(kinds.has('binary') ? [row('Control rate', pill('pControl', {label: 'Control response rate'}), 'For each yes-or-no outcome.'),
            row('Treatment rate', pill('pTreatment', {label: 'Treatment response rate'}), 'And with treatment.')] : []),
          ...(kinds.has('continuous') ? [row('Expected difference', pill('effect', {label: 'Expected difference'}), 'For each measured outcome.'),
            row('Standard deviation', pill('sd', {label: 'Standard deviation'}), 'Of one participant\'s outcome.')] : []),
          row('Correlation', pill('correlation', {label: 'Correlation between outcomes'}), 'How strongly the outcomes move together in one participant, from 0 to below 1.')),
        note('Each outcome\'s power, the chance of rejecting any and all, simulated with the family\'s procedure.')] : [])]);
  }

  function paintOneArm() {
    const estimate = state.aim === 'estimate';
    oneArmTest.hidden = estimate;
    oneArmEstimate.hidden = !estimate;
    oneArmLevel.hidden = estimate;
    // Estimating a rate can ask how many for a margin of error; testing one, for power.
    const offered = estimate ? ['none', 'precision'] : ['none', 'plan', 'data'];
    if (!offered.includes(state.add)) state.add = 'none';
    swap(oneArmAlso, 'one' + estimate, () => [heading('Also'), segments('add-one', estimate ?
      {none: {label: 'Nothing more', glyph: 'none'}, precision: {label: 'Find the size for a margin of error', glyph: 'interval'}} :
      {none: {label: 'Nothing more', glyph: 'none'}, plan: {label: 'Find the sample size', glyph: 'target'}, data: {label: 'Analyse results', glyph: 'table'}}, pick('add'), 'add')]);
    oneArmCount.hidden = estimate || state.add !== 'data';
    const precise = estimate && state.add === 'precision';
    if (precise && state.moe === undefined) Object.assign(state, marginDefaults('response_rate'));
    oneArmPrecision.hidden = !precise;
    swap(oneArmPrecision, precise ? 'precision' + state.marginKind : 'none', () => !precise ? [] : [
      rows(row('Expected rate', pill('base', {label: 'Expected rate'}), 'The response rate you expect, such as 3/10.')), ...marginRows()]);
  }

  function paintTwoStage() {
    if (state.rule === 'posterior') state.find = 'given';
    findBox.hidden = state.rule !== 'threshold';
    searchRows.hidden = state.rule !== 'threshold' || state.find !== 'search';
    givenRows.hidden = state.rule === 'threshold' && state.find === 'search';
    thresholdRows.hidden = state.rule !== 'threshold' || state.find !== 'given';
    posteriorRows.hidden = state.rule !== 'posterior';
  }

  function paintObserved() {
    const d = state.design;
    const scale = key => segments(key, {binary: {label: 'Yes or no', glyph: 'binary'}, continuous: {label: 'A measurement', glyph: 'continuous'}}, pick(key));
    swap(scalesBox, d, () => [
      ...(d === 'cohort' || d === 'cross_sectional' ? [part(heading('The outcome is'), scale('outcomeScale'))] : []),
      ...(d === 'cross_sectional' ? [part(heading('The exposure is'), scale('exposureScale'))] : [])]);
    populationBox.hidden = d !== 'cohort';
    surveyBox.hidden = d !== 'cross_sectional';
    surveyClusters.hidden = d !== 'cross_sectional' || state.survey !== 'cluster';
    const fixedTotal = d === 'cross_sectional' || (d === 'cohort' && state.population);
    swap(groupSizes, d + fixedTotal, () => {
      const n = (key, label) => pill(key, {numeric: true, label});
      return [d === 'person_time' ? note('A person-time cohort fixes no group size: person-time is followed, and events are counted.') :
        d === 'matched_case_control' ? sentence(n('cases', 'Matched pairs'), 'matched pairs: each case with one control') :
          d === 'case_control' ? sentence(n('cases', 'Cases'), 'cases and', n('controls', 'Controls'), 'controls') :
            fixedTotal ? sentence(n('total', 'Participants'), 'participants in all') :
              sentence(n('exposed', 'Exposed'), 'exposed and', n('unexposed', 'Unexposed'), 'unexposed')];
    });
    const tests = observedTests(state);
    state.test = observedTest(state);
    swap(observedTestBox, tests.join(), () => [tiles('observed-test', Object.fromEntries(tests.map(id =>
      [id, {...OBSERVED_TESTS[id], glyph: OBSERVED_TESTS[id].covariates ? 'adjust' : OBSERVED_TESTS[id].module === 'tests.correlation' ? 'correlation' :
        OBSERVED_TESTS[id].module === 'tests.survey' ? 'survey' : 'differ'}])), pick('test'), {key: 'test'})]);
    covariatesRow.hidden = !OBSERVED_TESTS[state.test].covariates;
    const extras = observedExtras(state);
    const options = {none: {label: 'Nothing more', glyph: 'none'}};
    if (extras.plan) options.plan = {label: d === 'person_time' ? 'Find the events needed' : 'Find the sample size', glyph: 'target'};
    if (extras.precision) options.precision = {label: 'Find the size for a margin of error', glyph: 'interval'};
    if (extras.data) options.data = {label: 'Analyse results', glyph: 'table'};
    if (!options[state.add]) state.add = 'none';
    swap(observedAlso, Object.keys(options).join() + d, () => [heading('Also'), segments('add-observed', options, pick('add'), 'add'),
      ...(extras.plan ? [] : [note('This test has no sample-size calculation yet; the proved tests have exact ones.')])]);
    const kind = observedPlanKind(state);
    observedPlan.hidden = state.add !== 'plan';
    const effect = needsDesignEffect(state);
    const skews = skewable(state);
    swap(observedPlan, state.add === 'plan' ? kind + effect + skews : 'none', () => state.add !== 'plan' ? [] : [
      ...PLAN_FIELDS[kind].map(([key, label, hint]) => row(label, pill(key, {label}), hint)),
      ...(effect ? [row('Design effect', pill('deff', {label: 'Design effect'}), 'The survey\'s variance over a simple random sample\'s, such as 2.')] : []),
      // Skewed data are simulated, and the test's Type I error judged.
      ...(skews ? [row('Outcome skewness', pill('skewY', {label: 'Skewness of the outcome\'s error'}), 'From -4 to 4; 0 for normal. Above 0, power is simulated.'),
        row('Exposure skewness', pill('skewX', {label: 'Skewness of the exposure'}), 'From -4 to 4; incomes are often near 3.')] : [])]);
    const precise = state.add === 'precision' && extras.precision;
    observedPrecision.hidden = !precise;
    const measure = precise ? precisionMeasure(state) : null;
    if (precise && (state.moe === undefined || state.precisionMeasure !== measure)) {
      state.precisionMeasure = measure;
      Object.assign(state, marginDefaults(measure));
    }
    swap(observedPrecision, precise ? [d, state.population, measure, state.marginKind, effect, state.survey].join() : 'none', () => !precise ? [] : [
      part(heading('Which interval?'), tiles('precision-measure', Object.fromEntries(Object.entries(precisionMeasures(state)).map(([id, info]) =>
        [id, {...info, glyph: 'interval'}])), choosePrecision, {key: 'precisionMeasure'})),
      rows(...precisionFields(state).map(([key, label, hint]) => row(label, pill(key, {label}), hint)),
        ...(needsDesignEffect({...state, test: 'survey_logistic'}) ? [row('Design effect', pill('deff', {label: 'Design effect'}), 'The survey\'s variance over a simple random sample\'s, such as 2.')] : [])),
      ...marginRows()]);
    observedData.hidden = state.add !== 'data';
    const table = {...defaultTable(state), ...(state.table || {})};
    const pairs = {...defaultPairs(state), ...(state.pairs || {})};
    // Until a count is typed, the table follows the sizes; after that it keeps what was typed.
    const dataKey = state.add !== 'data' ? 'none' : d === 'person_time' ? 'events' :
      d === 'matched_case_control' ? (state.pairs ? 'pairs-typed' : 'pairs' + JSON.stringify(pairs)) :
        (state.table ? 'table-typed' + d : 'table' + JSON.stringify(table) + d);
    swap(observedData, dataKey, () => {
      if (state.add !== 'data') return [];
      if (d === 'person_time') {
        return [rows(row('Exposed', sentence(pill('exposedEvents', {numeric: true, label: 'Exposed events'}), 'events in', pill('exposedTime', {label: 'Exposed person-time'}), 'person-years')),
          row('Unexposed', sentence(pill('unexposedEvents', {numeric: true, label: 'Unexposed events'}), 'events in', pill('unexposedTime', {label: 'Unexposed person-time'}), 'person-years')))];
      }
      // Counts in a grid, as a 2x2 table is read.
      const grid = (cells, heads, holder, typed, start) => {
        const node = el('div', 'wizard-grid');
        node.append(el('span'), ...heads.cols.map(h => el('span', 'wizard-grid-head', h)));
        cells.forEach((rowCells, i) => {
          node.append(el('span', 'wizard-grid-head row', heads.rows[i]));
          for (const key of rowCells) {
            const cell = pill('', {numeric: true, label: heads.rows[i] + ', ' + heads.cols[rowCells.indexOf(key)], onInput: v => {
              state[holder] = {...(state[holder] || start), [key]: v};
              observedData.dataset.swap = typed;
            }});
            cell.value = start[key];
            cell.dataset.slot = key;
            node.append(cell);
          }
        });
        return node;
      };
      if (d === 'matched_case_control') {
        return [heading('Observed pairs'), grid([['bothExposed', 'controlExposedOnly'], ['caseExposedOnly', 'neitherExposed']],
          {rows: ['Case exposed', 'Case unexposed'], cols: ['Control exposed', 'Control unexposed']}, 'pairs', 'pairs-typed', pairs)];
      }
      return [heading('Observed table'), grid([['exposedCases', 'exposedNoncases'], ['unexposedCases', 'unexposedNoncases']],
        {rows: ['Exposed', 'Unexposed'], cols: ['Cases', d === 'case_control' ? 'Controls' : 'Noncases']}, 'table', 'table-typed' + d, table)];
    });
  }

  const shown = new Map();
  function paintBlocks(source) {
    const blocks = blocksOf(source);
    const families = Object.fromEntries(blocks.map(b => [b.name, b.family]));
    const keep = new Set();
    for (const block of blocks) {
      const sig = JSON.stringify(block);
      let node = shown.get(block.name);
      const fresh = !node;
      if (fresh) {
        node = el('div', 'wiz-block fresh');
        node.dataset.name = block.name;
        node.addEventListener('animationend', () => node.classList.remove('fresh', 'bump'));
        shown.set(block.name, node);
      }
      node.dataset.family = block.family;
      // The blocks this step shapes are ringed and open; the rest fold to one line.
      const lit = LIT[at].includes(block.family);
      node.classList.toggle('lit', lit);
      node.classList.toggle('folded', !lit);
      if (node.dataset.sig !== sig) {
        if (!fresh) { node.classList.remove('bump', 'fresh'); void node.offsetWidth; node.classList.add('bump'); }
        node.dataset.sig = sig;
        const top = el('div', 'wiz-top');
        top.append(el('span', 'wiz-name', block.name), el('span', 'wiz-call', block.words));
        const inputs = el('div', 'wiz-inputs');
        for (const input of block.inputs) {
          if (input.key) inputs.append(el('span', 'wiz-key', input.key.replaceAll('_', ' ')));
          const value = el('span', 'wiz-pill' + (input.ref || input.call ? ' ref' : ''), input.value.replace(/^"|"$/g, ''));
          if (input.ref) value.dataset.family = families[input.value] || 'value';
          if (input.call) value.dataset.family = input.call;
          inputs.append(value);
        }
        node.replaceChildren(top, ...(block.inputs.length ? [inputs] : []));
      }
      // Move a block only when the order changes: moving it would replay its animation.
      const place = stack.children[keep.size] || null;
      if (place !== node) stack.insertBefore(node, place);
      keep.add(block.name);
    }
    for (const [key, node] of shown) if (!keep.has(key)) { node.remove(); shown.delete(key); }
  }

  function paintVerdict(made) {
    const words = [EVIDENCE[made.evidence].sentence, ...(made.notes || [])];
    const key = made.test + made.evidence + words.join();
    verdict.dataset.evidence = made.evidence;
    grade.dataset.evidence = made.evidence;
    if (verdict.dataset.key === key) return;
    verdict.dataset.key = key;
    const text = el('div', 'wizard-verdict-words');
    text.append(el('strong', '', TEST_WORDS[made.test] || made.test), el('p', '', words.join(' ')));
    verdict.replaceChildren(seal(made.evidence), text);
    grade.replaceChildren(seal(made.evidence), el('span', '', EVIDENCE[made.evidence].label));
  }

  paint();
  box.append(form);
  back.append(box);
  document.body.append(back);
  if (start.design) show(route()[1]);
  else search.focus({preventScroll: true});
  return {close};
}
