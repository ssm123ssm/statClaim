// Shared helpers for the shell, the palette and the canvas.

export function el(tag, cls, text) {
  const node = document.createElement(tag);
  if (cls) node.className = cls;
  if (text !== undefined && text !== null) node.textContent = text;
  return node;
}

export function button(label, action, cls = 'btn') {
  const node = el('button', cls, label);
  node.type = 'button';
  if (action) node.addEventListener('click', action);
  return node;
}

export const human = name => String(name).replaceAll('_', ' ');
export const title = name => String(name).replace(/\.stat$/i, '').replaceAll('_', ' ');

const SVG = 'http://www.w3.org/2000/svg';
const PATHS = {
  check: 'M4 10.5l4 4 8-9',
  alert: 'M10 3l8 14H2L10 3zm0 5v4m0 2.5v.5',
  info: 'M10 2.5a7.5 7.5 0 100 15 7.5 7.5 0 000-15zm0 5v6m0-8.5v.5',
  x: 'M5 5l10 10M15 5L5 15',
  plus: 'M10 4v12M4 10h12',
  minus: 'M4 10h12',
  grid: 'M3.5 3.5h5v5h-5zM11.5 3.5h5v5h-5zM3.5 11.5h5v5h-5zM11.5 11.5h5v5h-5z',
  copy: 'M7 7h9v9H7zM4 13V4h9',
  down: 'M10 5v10m-4-4l4 4 4-4',
  collapse: 'M4 6h12M4 10h12M4 14h7',
  expand: 'M4 5h12M4 9h12M4 13h12M4 17h12',
  more: 'M4.5 10h.01M10 10h.01M15.5 10h.01',
  undo: 'M7 6L3 10l4 4M3.5 10H12a5 5 0 010 10h-2',
  redo: 'M13 6l4 4-4 4M16.5 10H8a5 5 0 000 10h2',
  file: 'M5 2.5h6.5L15 6v11.5H5zM11 2.5V6h4',
  open: 'M2.5 6V15.5h15V7.5H9L7.5 5.5h-5zM2.5 8h15',
  save: 'M10 3v9m-4-4l4 4 4-4M4 14.5v2h12v-2',
  restore: 'M3.5 10a6.5 6.5 0 102-4.7M3 3v4h4',
  search: 'M8.5 3.5a5 5 0 100 10 5 5 0 000-10zM12.2 12.2L17 17',
  panel: 'M3 4h14v12H3zM12.5 4v12',
  chevron: 'M6 8l4 4 4-4',
  up: 'M10 15V5m-4 4l4-4 4 4',
  link: 'M8.5 11.5l3-3M7 9L5.5 10.5a2.5 2.5 0 003.5 3.5L10.5 12.5M13 11l1.5-1.5a2.5 2.5 0 00-3.5-3.5L9.5 7.5',
  lock: 'M6.5 9V6.5a3.5 3.5 0 017 0V9M4.5 9h11v8h-11zM10 12.5v1.5',
  play: 'M6 4l10 6-10 6z',
  code: 'M7 6l-4 4 4 4M13 6l4 4-4 4',
  book: 'M3 4.5c2.5-1 5-1 7 .5 2-1.5 4.5-1.5 7-.5v11c-2.5-1-5-1-7 .5-2-1.5-4.5-1.5-7-.5z M10 5v11',
  grip: 'M7.5 5h.01M12.5 5h.01M7.5 10h.01M12.5 10h.01M7.5 15h.01M12.5 15h.01',
  note: 'M4 3.5h12v9l-4 4H4zM12 16.5v-4h4',
  pencil: 'M12.5 4.5l3 3L7 16H4v-3z',
  trash: 'M4 6h12M8 6V4h4v2M5.5 6l1 10.5h7l1-10.5',
  fold: 'M6 12l4-4 4 4',
  target: 'M10 3v3m0 8v3M3 10h3m8 0h3M10 7a3 3 0 100 6 3 3 0 000-6z',
  spark: 'M10 2.5l1.8 5.7 5.7 1.8-5.7 1.8L10 17.5l-1.8-5.7L2.5 10l5.7-1.8z',
  dice: 'M5 3.5h10a1.5 1.5 0 011.5 1.5v10a1.5 1.5 0 01-1.5 1.5H5A1.5 1.5 0 013.5 15V5A1.5 1.5 0 015 3.5zM7 7h.01M13 13h.01M10 10h.01M13 7h.01M7 13h.01',
  flow: 'M2.5 4h5v4h-5zM12.5 12h5v4h-5zM7.5 6h2.5v8h2.5',
  fit: 'M3 7.5V3h4.5M12.5 3H17v4.5M17 12.5V17h-4.5M7.5 17H3v-4.5',
  history: 'M10 3.5a6.5 6.5 0 11-6.1 4.3M3.5 3.5V8H8M10 6.5V10l2.5 2',
};

export function icon(name, cls = 'icon') {
  const svg = document.createElementNS(SVG, 'svg');
  svg.setAttribute('viewBox', '0 0 20 20');
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('class', cls);
  const path = document.createElementNS(SVG, 'path');
  path.setAttribute('d', PATHS[name] || PATHS.info);
  svg.append(path);
  return svg;
}

export function iconButton(name, label, action, cls = 'icon-btn') {
  const node = button('', action, cls);
  node.append(icon(name));
  node.setAttribute('aria-label', label);
  node.title = label;
  return node;
}

// Colour follows the type a block produces, so an opening shows which blocks fit it.
const FAMILY_OF = {
  Model: 'study', Assignment: 'study', Outcome: 'study', OutcomeModel: 'study', Stratum: 'study',
  OneArmModel: 'study', TwoStageModel: 'study',
  StudyDesign: 'design', Prior: 'design', Rule: 'design',
  Hypothesis: 'null', OutcomeNull: 'null', SharpNull: 'null',
  Analysis: 'analysis', CitedAnalysis: 'analysis', RandomisationAnalysis: 'analysis',
  OneSampleAnalysis: 'analysis', TwoStageAnalysis: 'analysis',
  // One question asked at several looks: claims take it where they take an analysis.
  Sequential: 'analysis',
  // A t-test whose size is re-estimated: claims take it where they take an analysis.
  Reestimation: 'analysis',
  Family: 'family', ComposedFamily: 'family',
  // Observational studies: exposure was not assigned.
  ObservationalStudy: 'study', CrossSectionalStudy: 'study', CohortStudy: 'study', CaseControlStudy: 'study',
  AssociationNull: 'null', AssociationAnalysis: 'analysis', AssociationTable: 'data',
  MatchedStudy: 'study', MatchedAnalysis: 'analysis', MatchedPairs: 'data',
  PersonTimeStudy: 'study', RateAnalysis: 'analysis', ObservedEvents: 'data',
  CitedAssociation: 'analysis',
  Observation: 'data', OneSampleObservation: 'data', TwoStageObservation: 'data',
  Rates: 'planning', Rate: 'planning', MeanDifference: 'planning', HazardRatio: 'planning',
  PowerTarget: 'planning', Candidates: 'planning', OneArmCandidates: 'planning',
  TwoStageCandidates: 'planning', LookCandidates: 'planning', PlanningPoint: 'planning', Feasibility: 'planning', Sizing: 'planning',
  // Planning points and searches of observational studies.
  Risks: 'planning', ExposurePrevalence: 'planning', OutcomePrevalence: 'planning',
  DiscordantPairs: 'planning', IncidenceRates: 'planning',
  GroupCandidates: 'planning', CountCandidates: 'planning', TotalCandidates: 'planning',
  // Cluster-randomised trials, searched by clusters per arm or by cluster size.
  ClusterCandidates: 'planning', ExponentialSurvival: 'planning', Correlation: 'planning', Slope: 'planning', OddsPerSd: 'planning', OutcomeMeans: 'planning',
  // Precision: a planned interval, its target, its point and its sizes.
  SingleProportion: 'planning', PrecisionTarget: 'planning', PlannedInterval: 'planning', IntervalCandidates: 'planning',
  NullScenarios: 'planning', EndpointPoints: 'planning',
  EstimableModel: 'study', Target: 'planning',
  Claim: 'claim', VerificationResult: 'run', CalculationResult: 'run',
  list: 'list',
};
const SCALARS = new Set(['integer', 'number', 'exact number', 'level', 'string']);

export const FAMILIES = {
  study: 'Study model',
  design: 'Design',
  null: 'Null hypothesis',
  analysis: 'Analysis',
  family: 'Multiplicity',
  claim: 'Claim',
  run: 'Check',
  planning: 'Planning',
  data: 'Observed data',
  list: 'List',
  value: 'Value',
  other: 'Value',
};

export function familyOf(type) {
  if (!type) return 'other';
  const inner = String(type).match(/^Option\[(.*)\]$/)?.[1] || type;
  if (SCALARS.has(inner)) return 'value';
  if (FAMILY_OF[inner]) return FAMILY_OF[inner];
  if (/Claim$/.test(inner)) return 'claim';
  if (/Interval/.test(inner)) return 'analysis';
  return 'other';
}

// Why a contract passed: the checked derivation, in words. Fitting is not proof; the note says so.
export function derivationView(entry) {
  const d = entry.derivation;
  const strip = text => String(text || '').replace(new RegExp('^' + entry.name + ': '), '');
  const box = el('div', 'why');
  const lead = strip(d.conclusion);
  box.append(el('p', 'why-conclusion', lead.charAt(0).toUpperCase() + lead.slice(1)));
  if (d.guarantee?.sentence) {
    const line = el('p', 'why-guarantee');
    const grade = d.guarantee.grade || 'proved';
    line.append(el('span', 'why-grade why-grade-' + grade, grade === 'proved' ? 'checked in Lean' : grade), ' ', d.guarantee.sentence);
    box.append(line);
  }
  const steps = el('ol', 'why-steps');
  for (const step of d.steps || []) {
    const item = el('li', 'why-step');
    const said = strip(step.conclusion);
    item.append(el('span', 'why-rule', step.rule.replaceAll('-', ' ')), el('span', 'why-text', said.charAt(0).toUpperCase() + said.slice(1)));
    item.title = step.premise || '';
    steps.append(item);
  }
  box.append(el('h4', 'why-head', 'Why it fits'), steps);
  if (d.assumptions?.length) {
    const list = el('ul', 'why-list');
    for (const text of d.assumptions) list.append(el('li', '', text));
    box.append(el('h4', 'why-head', 'Assumptions you must meet in the real study'), list);
  }
  if (d.obligations?.length) {
    const list = el('ul', 'why-list why-open');
    for (const item of d.obligations) list.append(el('li', '', typeof item === 'string' ? item : item.text || item.message || JSON.stringify(item)));
    box.append(el('h4', 'why-head', 'Still open'), list);
  }
  if (d.not_established) box.append(el('p', 'why-note', d.not_established));
  box.append(el('p', 'why-check' + (entry.checked ? '' : ' why-failed'), entry.checked ?
    'An independent checker re-derived every step. This shows the pieces fit; Run checks establishes the guarantee.' :
    'The independent checker found problems: ' + (entry.problems || []).join(' ')));
  return box;
}

// Each kind of value has a connector shape on its left edge, and an input shows the shape it takes.
// The open side of each path (x = 8) joins the block; the shape protrudes to the left.
const KEYS = {
  study: 'M8 1C3.6 1 1 4.2 1 8s2.6 7 7 7',
  design: 'M8 2H3.2Q2 2 2 3.2V12.8Q2 14 3.2 14H8',
  null: 'M8 .6L1.2 8 8 15.4',
  analysis: 'M8 1L1.6 4.6v6.8L8 15',
  family: 'M8 1C4.4 1 2.2 2.6 2.2 4.5S4.4 8 8 8C4.4 8 2.2 9.6 2.2 11.5S4.4 15 8 15',
  claim: 'M8 1H1.2L4.4 8 1.2 15H8',
  data: 'M8 1H3.6L1.2 4.5 3.6 8 1.2 11.5 3.6 15H8',
  planning: 'M8 1H4.4v4H1.4v6h3v4H8',
  list: 'M8 1H1.6v14H8v-2.8H4.6V3.8H8',
};
export const SHAPES = {
  study: 'round', design: 'square', null: 'pointed', analysis: 'bevelled', family: 'double',
  claim: 'notched', data: 'zigzag', planning: 'stepped', list: 'bracket',
};
export function keyShape(family, cls = 'key') {
  if (!KEYS[family]) return null;
  const svg = document.createElementNS(SVG, 'svg');
  svg.setAttribute('viewBox', '0 0 8 16');
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('class', cls);
  svg.setAttribute('data-shape', family);
  const path = document.createElementNS(SVG, 'path');
  path.setAttribute('d', KEYS[family]);
  svg.append(path);
  return svg;
}
// A connector drawn in its own family's colour, for chips, options and the legend.
export function keyGlyph(family, cls = 'key key-inline') {
  const svg = keyShape(family, cls);
  svg?.setAttribute('data-family', family);
  return svg;
}

export function setFamily(node, type) {
  node.dataset.family = familyOf(type);
  return node;
}

// Diagnostic codes are short identifiers. These read better as headings.
const CODE_TITLES = {
  syntax: 'Syntax error',
  type: 'Wrong kind of value',
  arguments: 'Inputs do not match',
  domain: 'Value out of range',
  obligation: 'Guarantee not established',
  allocation: 'Error budget exceeded',
  unknown_module: 'Unknown module',
  unknown_field: 'Unknown field',
  redefinition: 'Name used twice',
  duplicate_analysis: 'Same question asked twice',
  sampling_scope: 'Design does not fit',
  sampling_contract: 'Design does not fit the test',
  unsupported_claim: 'Claim not supported',
  finite_sample: 'Finite-sample check',
  unit_mismatch: 'Units do not match',
  never_rejects: 'Test can never reject',
  alternative_in_null: 'Alternative lies inside the null',
  cited: 'Cited guarantee',
  declared: 'Declared guarantee',
  conditional: 'Conditional guarantee',
  undeclared_randomisation: 'Randomisation not declared',
  empty_input: 'Empty input',
};

export function codeTitle(code) {
  if (CODE_TITLES[code]) return CODE_TITLES[code];
  const text = human(code || 'problem');
  return text.charAt(0).toUpperCase() + text.slice(1);
}

export function statusText(status) {
  if (!status || status === 'elaborated') return 'Compiles';
  const text = human(status);
  return text.charAt(0).toUpperCase() + text.slice(1);
}

export function plural(count, word, many = word + 's') {
  return count + ' ' + (count === 1 ? word : many);
}

// Long compiler messages read better as a lead sentence and optional detail.
export function splitMessage(message) {
  const sentences = String(message).split(/(?<=[.;])\s+(?=[A-Z])/);
  let count = 1;
  while (count < sentences.length && sentences.slice(0, count).join(' ').length < 70) count++;
  return {lead: sentences.slice(0, count).join(' '), rest: sentences.slice(count).join(' ')};
}

export function messageBlock(message, cls = 'msg') {
  const {lead, rest} = splitMessage(message);
  const box = el('div', cls);
  box.append(el('p', 'msg-lead', lead));
  if (rest) {
    const more = el('details', 'msg-more');
    more.append(el('summary', '', 'More detail'), el('p', '', rest));
    box.append(more);
  }
  return box;
}

// Run results. A grade is never shown as stronger than the weakest part inside a claim.
export const GRADE_ORDER = ['proved', 'conditional', 'cited', 'declared'];
const OUTCOMES = {
  verified: ['proved', 'Proved in Lean', 'check'],
  conditional: ['conditional', 'Combination proved; members assumed', 'check'],
  cited: ['cited', 'Cited, not machine-checked', 'book'],
  declared: ['declared', 'Declared by the author, not checked', 'alert'],
  calculated: ['calculated', 'Calculated, no certificate', 'spark'],
  simulated: ['simulated', 'Simulated, not a proof', 'dice'],
  unresolved_obligation: ['open', 'Not established', 'alert'],
  backend_error: ['error', 'The backend failed', 'x'],
  not_executed: ['open', 'Not run', 'info'],
  needs_lean: ['open', 'Needs Lean to prove it', 'lock'],
  stale_source: ['open', 'Source changed during the run', 'alert'],
};
const STATUS_GRADE = {verified: 'proved', conditional: 'conditional', cited: 'cited', declared: 'declared'};
export const SCOPE_TEXT = {finite_sample: 'finite-sample bound', asymptotic: 'large-sample approximation'};

export function outcome(request) {
  const [tone, label, iconName] = OUTCOMES[request.status] || ['open', human(request.status || 'unknown'), 'info'];
  const own = STATUS_GRADE[request.status];
  const link = request.weakest_link;
  const weaker = own && link && GRADE_ORDER.indexOf(link.grade) > GRADE_ORDER.indexOf(own) ? link : null;
  return {tone, label, icon: iconName, scope: SCOPE_TEXT[request.evidence?.scope], weakest: weaker};
}

// Short labels for tight places, such as the tray under a block; the full label is the tooltip.
const SHORT = {conditional: 'Combination proved', cited: 'Cited', declared: 'Declared', calculated: 'Calculated', simulated: 'Simulated', backend_error: 'Backend failed', stale_source: 'Source changed', needs_lean: 'Needs Lean'};

export function outcomeBadge(request, cls = 'outcome', short = false) {
  const info = outcome(request);
  const badge = el('span', cls);
  badge.dataset.tone = info.tone;
  const label = short && SHORT[request.status] || info.label;
  badge.append(icon(info.icon), el('span', '', label));
  if (label !== info.label) badge.title = info.label;
  return badge;
}

// A calculated number arrives as a string, a number or an exact fraction record.
export function numberValue(value) {
  if (value === null || value === undefined || value === '') return NaN;
  if (typeof value === 'object') return numberValue(value.decimal_approximation ?? value.fraction);
  const [a, b] = String(value).split('/');
  return b === undefined ? Number(a) : Number(a) / Number(b);
}
// A share as a percentage, with enough digits to tell it apart from a nearby target.
export function percent(value, beside) {
  const v = numberValue(value) * 100;
  if (!Number.isFinite(v)) return '';
  const target = numberValue(beside) * 100;
  const near = Number.isFinite(target) ? target : null;
  let digits = Math.abs(v) < 10 && v !== 0 ? 2 : 1;
  while (near !== null && digits < 4 && v !== near && +v.toFixed(digits) === +near.toFixed(digits)) digits++;
  return +v.toFixed(digits) + '%';
}
const short = value => {
  const v = numberValue(value);
  return Number.isFinite(v) ? String(+v.toPrecision(3)) : String(value ?? '');
};
// The sizes a planning result is about, in words.
export function sizeText(c) {
  if (c.n_stage1 !== undefined && c.n_stage2 !== undefined) return c.n_stage1 + ' then ' + c.n_stage2;
  // A cluster trial, in clusters and their size.
  if (c.clusters_control !== undefined) {
    const [kc, kt, mc, mt] = [c.clusters_control, c.clusters_treatment, short(c.cluster_size_control), short(c.cluster_size_treatment)];
    // Simulated clusters of unequal sizes have these sizes on average.
    const varied = c.cluster_size_cv && numberValue(c.cluster_size_cv) > 0 ? ' on average' : '';
    return (kc === kt && mc === mt ? kc + ' clusters of ' + mc + ' per arm' : kc + ' and ' + kt + ' clusters of ' + mc + ' and ' + mt) + varied;
  }
  if (c.n_control !== undefined && c.n_treatment !== undefined) {
    // A survival plan from times also says how many events the size expects.
    const events = c.expected_events !== undefined ? ' (about ' + Math.round(numberValue(c.expected_events)) + ' events)' : '';
    return (c.n_control === c.n_treatment ? c.n_control + ' per arm' : c.n_control + ' and ' + c.n_treatment) + events;
  }
  // Observational studies, in the units their design fixes.
  if (c.cases !== undefined && c.controls !== undefined) return c.cases + ' cases and ' + c.controls + ' controls';
  if (c.exposed !== undefined && c.unexposed !== undefined) return c.exposed + ' exposed and ' + c.unexposed + ' unexposed';
  if (c.pairs !== undefined) return c.pairs + ' pairs';
  if (c.events !== undefined) return c.events + ' events';
  if (c.exposed_share !== undefined && c.total_sample_size !== undefined) return 'n = ' + c.total_sample_size;
  // A precision search over one population.
  if (c.margin_achieved !== undefined && c.total_sample_size !== undefined && c.covariates === undefined) return 'n = ' + c.total_sample_size;
  // A cited observational test: its total, with the covariates it adjusts for.
  if (c.covariates !== undefined && c.total_sample_size !== undefined) {
    // A complex survey is worth fewer independent participants: say how many.
    const effective = c.effective_sample_size !== undefined ? ' (effectively ' + Math.round(numberValue(c.effective_sample_size)) + ')' : '';
    return 'n = ' + c.total_sample_size + effective;
  }
  if (c.n !== undefined) return 'n = ' + c.n;
  return '';
}
// The bounds of a search, whatever it searched: arm sizes, totals, cases, pairs or events.
const SEARCH_BOUNDS = ['n', 'per_arm', 'cases', 'exposed', 'pairs', 'events', 'clusters_per_arm', 'cluster_size', 'size'];
const searchBound = (c, side) => {
  for (const key of SEARCH_BOUNDS) if (c[side + '_' + key] !== undefined) return c[side + '_' + key];
  return side === 'max' ? c.max_total : undefined;
};
const firstSentence = text => {
  const lead = String(text).split(/(?<=[.;])\s+(?=[A-Z])/)[0];
  return lead.length > 140 ? lead.slice(0, 137) + '…' : lead;
};
// What a run found, in one line: the numbers behind the grade. Tone is 'ok' or 'warn' when it meets or misses a target.
export function headline(request) {
  const c = request.calculation || {};
  const decision = request.decision;
  if (decision === 'no_feasible_candidate') {
    const low = searchBound(c, 'min');
    const high = searchBound(c, 'max');
    // A search of cluster sizes says how far more participants can go: only to the ceiling.
    const ceiling = c.power_ceiling !== undefined ? '; with these clusters power cannot pass ' + percent(c.power_ceiling) : '';
    return {text: 'No size' + (low !== undefined && high !== undefined ? ' from ' + low + ' to ' + high : ' in the range') + ' meets the target' + ceiling, tone: 'warn'};
  }
  // A precision target: the margin of error reached, and the assurance when asked.
  if (c.margin_achieved !== undefined || c.precision_target_met !== undefined && c.target_margin !== undefined) {
    const searched = c.candidates_evaluated !== undefined;
    const size = sizeText(c) || (c.total_sample_size !== undefined ? 'n = ' + c.total_sample_size : '');
    const show = record => record == null ? 'unbounded' : (c.relative ? percent(record) : '±' + short(record));
    const target = c.relative ? percent(c.target_margin) : '±' + short(c.target_margin);
    const words = c.relative ? 'relative margin ' : 'margin ';
    const assured = c.assurance !== undefined ? ', assurance ' + percent(c.assurance, c.minimum_assurance) : '';
    let text = searched
      ? (c.assurance !== undefined ? 'Sufficient size: ' : 'Smallest size: ') + size + ', ' + words + show(c.margin_achieved) + assured
      : words.replace(/^./, ch => ch.toUpperCase()) + show(c.margin_achieved) + (size ? ' at ' + size : '') + assured;
    if (c.precision_target_met === false) text += ', short of the ' + target + ' target' + (c.assurance !== undefined ? ' with ' + percent(c.minimum_assurance) + ' assurance' : '');
    return {text, tone: c.precision_target_met === false ? 'warn' : 'ok'};
  }
  if (c.power !== undefined && c.minimum_power !== undefined) {
    const searched = c.candidates_evaluated !== undefined;
    const size = sizeText(c);
    // A simulated power carries its 95% interval.
    const range = c.power_lower !== undefined ? ' (' + percent(c.power_lower).replace('%', '') + '–' + percent(c.power_upper) + ')' : '';
    let text = searched
      ? (c.n_stage1 !== undefined ? 'Chosen design: ' : 'Smallest size: ') + size + ', power ' + percent(c.power, c.minimum_power) + range
      : 'Power ' + percent(c.power, c.minimum_power) + range + (size ? ' at ' + size : '');
    if (decision === 'undecided') {
      // Undecided on Type I only when power is settled and the judged Type I is not.
      const typeIOpen = c.typeI_judged && c.typeI_target_met === false && c.typeI_settled === false;
      const powerOpen = c.power_target_met === false && c.power_settled === false;
      const why = typeIOpen && !powerOpen ? 'the type I interval includes the ' + percent(c.maximum_typeI) + ' limit' : 'the interval includes the ' + percent(c.minimum_power) + ' target';
      return {text: text + ': undecided, ' + why, tone: 'warn'};
    }
    if (c.power_target_met === false) text += ', below the ' + percent(c.minimum_power) + ' target';
    else if (!searched) text += ', meets the ' + percent(c.minimum_power) + ' target';
    if (c.typeI_target_met === false && c.typeI !== undefined) text += '; type I error ' + percent(c.typeI, c.maximum_typeI) + ' is above ' + percent(c.maximum_typeI);
    return {text, tone: c.power_target_met === false || c.typeI_target_met === false ? 'warn' : 'ok'};
  }
  if (c.lower !== undefined && c.upper !== undefined) {
    const level = c.level !== undefined ? percent(c.level) + ' ' : '';
    return {text: 'Estimate ' + short(c.estimate) + ', ' + level + 'interval ' + short(c.lower) + ' to ' + short(c.upper), tone: null};
  }
  if (['reject_null', 'do_not_reject_null', 'do_not_reject'].includes(decision)) {
    const text = (decision === 'reject_null' ? 'Reject the null' : 'Do not reject the null') + (c.p_value !== undefined ? ', p = ' + short(c.p_value) : '');
    return {text, tone: null};
  }
  const guarantee = request.evidence?.guarantee;
  if (guarantee?.bound) return {text: human(guarantee.quantity || 'error').replace(/^./, ch => ch.toUpperCase()) + ' at most ' + guarantee.bound, tone: null};
  if (decision) return {text: human(decision).replace(/^./, ch => ch.toUpperCase()), tone: null};
  if (request.message) return {text: firstSentence(request.message), tone: null, title: request.message};
  return null;
}

// Dragging a number changes it in steps that suit what it is. Returns {px, at(steps, shift)} or null.
// Levels move along the usual ladder; rates between 0 and 1 move by hundredths and stay fractions;
// whole numbers move by one (Shift for ten); other numbers by a tenth of their leading digit.
const LEVELS = ['1/1000', '1/200', '1/100', '1/50', '1/40', '1/20', '1/10', '3/20', '1/5'];
const gcd = (a, b) => b ? gcd(b, a % b) : Math.abs(a);
export function scrubber(text, expected) {
  const written = String(text).replace(/\s+/g, '');
  const value = numberValue(written);
  if (!written || !Number.isFinite(value)) return null;
  const clamp = (n, low, high) => Math.min(high, Math.max(low, n));
  if (expected === 'level' && value > 0 && value < 1) {
    const levels = LEVELS.map(numberValue);
    // From a value off the ladder, the first step goes to the neighbour on that side.
    const below = levels.filter(level => level < value - 1e-12).length;
    const on = levels.findIndex(level => Math.abs(level - value) < 1e-12);
    return {px: 18, at: steps => {
      if (!steps) return written;
      const index = on >= 0 ? on + steps : steps > 0 ? below + steps - 1 : below + steps;
      return LEVELS[clamp(index, 0, LEVELS.length - 1)];
    }};
  }
  if (/^-?\d+$/.test(written)) {
    const start = Number(written);
    return {px: 7, at: (steps, shift) => !steps ? written : String(start >= 0 ? Math.max(0, start + steps * (shift ? 10 : 1)) : start + steps * (shift ? 10 : 1))};
  }
  if (Math.abs(value) < 1 && value !== 0) {
    const sign = Math.sign(value);
    const start = Math.round(Math.abs(value) * 100);
    return {px: 6, at: (steps, shift) => {
      if (!steps) return written;
      const hundredths = clamp(start + sign * steps * (shift ? 5 : 1), 1, 99);
      if (!written.includes('/')) return String(sign * hundredths / 100);
      const d = gcd(hundredths, 100);
      return (sign < 0 ? '-' : '') + hundredths / d + '/' + 100 / d;
    }};
  }
  const unit = 10 ** (Math.floor(Math.log10(Math.abs(value) || 1)) - 1);
  const digits = Math.max(0, -Math.round(Math.log10(unit)), (written.split('.')[1] || '').length);
  return {px: 7, at: (steps, shift) => !steps ? written : String(+(value + steps * unit * (shift ? 10 : 1)).toFixed(digits))};
}

// A value a run filled in, in a few words: {text, title}. Exact fractions read as decimals, with the fraction on hover.
export function valueText(value) {
  if (value === null || value === undefined) return {text: 'none', title: 'The run gave no value here'};
  if (typeof value === 'boolean') return {text: value ? 'yes' : 'no'};
  if (typeof value === 'number') return {text: String(value)};
  const exact = fraction => {
    const digits = fraction.replace(/^-/, '').split('/').map(part => part.length);
    return {text: String(+numberValue(fraction).toPrecision(4)),
      title: Math.max(...digits) <= 24 ? 'Exactly ' + fraction : 'An exact fraction with ' + digits.join('- and ') + '-digit terms'};
  };
  if (typeof value === 'string') return /^-?\d+\/\d+$/.test(value) ? exact(value) : {text: human(value)};
  if (Array.isArray(value)) {
    const parts = value.slice(0, 4).map(item => valueText(item)?.text ?? '…');
    return {text: parts.join(', ') + (value.length > 4 ? ', …' : '')};
  }
  if (typeof value === 'object') {
    if (value.fraction !== undefined) return exact(String(value.fraction).includes('/') ? value.fraction : value.fraction + '/1');
    if (value.grade) return {text: human(value.grade) + (SCOPE_TEXT[value.scope] ? ' · ' + SCOPE_TEXT[value.scope] : '')};
    const found = headline({calculation: value, decision: value.decision});
    if (found) return {text: found.text};
    if (value.status) return {text: human(value.status)};
  }
  return null;
}

// A number for reading: four significant digits, and a short exact fraction alongside. Long fractions go in the tooltip.
const decimal = value => {
  if (value === null || value === undefined) return '';
  if (typeof value !== 'object') return /^-?\d+\/\d+$/.test(String(value)) ? valueText(String(value)).text : String(value);
  const fraction = value.fraction === undefined ? '' : String(value.fraction);
  if (fraction && !fraction.includes('/')) return fraction;
  const approx = Number(value.decimal_approximation);
  return Number.isFinite(approx) ? String(Number(approx.toPrecision(4))) + (fraction && fraction.length <= 12 ? ' (' + fraction + ')' : '') : fraction;
};
const exactTitle = value => {
  const fraction = value && typeof value === 'object' ? value.fraction : value;
  return typeof fraction === 'string' && fraction.includes('/') && fraction.length > 12 ? valueText(fraction).title : undefined;
};
const DECISIONS = {reject_null: 'Reject the null', do_not_reject_null: 'Do not reject the null', do_not_reject: 'Do not reject the null'};

// Label, value and an optional tooltip for each number a calculation reports.
export function calculationLines(calculation, decision) {
  const c = calculation || {};
  const lines = [];
  if (decision) lines.push(['Decision', DECISIONS[decision] || human(decision).replace(/^./, ch => ch.toUpperCase())]);
  if (c.p_value) lines.push(['p-value', decimal(c.p_value), exactTitle(c.p_value)]);
  if (c.table) {
    const count = row => row[0] + ' of ' + (row[0] + row[1]);
    lines.push(['Data', 'control ' + count(c.table.control) + ', treatment ' + count(c.table.treatment)]);
  }
  if (c.responses !== undefined && c.n !== undefined) lines.push(['Data', c.responses + ' responses of ' + c.n]);
  if (c.estimate) lines.push(['Estimate', decimal(c.estimate)]);
  if (c.lower && c.upper) lines.push(['Interval', decimal(c.lower) + ' to ' + decimal(c.upper) + (c.level ? ', level ' + decimal(c.level) : '')]);
  const size = c.p_value === undefined && c.lower === undefined ? sizeText(c) : '';
  if (size) lines.push(['Size', size]);
  // Fisher's test at looks, summed exactly: each look's chance of stopping and the expected size.
  if (Array.isArray(c.looks) && c.power_lower === undefined) {
    lines.push(['Looks', c.looks.map(look => look.n_control + ' and ' + look.n_treatment + ': stops ' + percent(look.stop)).join('; '),
      'With both arms at the control rate: ' + c.looks.map(look => percent(look.stop_null)).join(', ')]);
    lines.push(['Expected size', Math.round(numberValue(c.expected_sample_size)) + ' participants',
      'With both arms at the control rate: ' + Math.round(numberValue(c.expected_sample_size_null))]);
    if (c.typeI_at_control_rate !== undefined) lines.push(['Exact Type I', percent(c.typeI_at_control_rate), 'Both arms at the control rate; the level is proved']);
  }
  if (c.power_lower !== undefined) {
    // Simulated: each estimate with its interval, then how it was simulated.
    // Percentages, as in the line above the numbers; each interval is 95%.
    const share = (value, low, high) => percent(value, low) + ' (' + percent(low).replace('%', '') + '–' + percent(high) + ')';
    lines.push(['Power', share(c.power, c.power_lower, c.power_upper) + ', target ' + percent(c.minimum_power),
      c.power_rejected === undefined ? undefined : c.power_rejected + ' of ' + Number(c.runs).toLocaleString('en') + ' simulated studies rejected']);
    lines.push(['Type I', share(c.typeI, c.typeI_lower, c.typeI_upper) + ', level ' + percent(c.alpha) +
      (c.typeI_judged ? ', judged against ' + percent(c.maximum_typeI) : ''),
      c.typeI_rejected === undefined ? undefined : 'At the null\'s boundary: ' + c.typeI_rejected + ' of ' + Number(c.runs).toLocaleString('en') + ' rejected']);
    // A family: each endpoint's power, and the chances of rejecting any and all.
    if (Array.isArray(c.endpoints)) {
      for (const endpoint of c.endpoints) {
        lines.push([human(endpoint.name).replace(/^./, ch => ch.toUpperCase()), share(endpoint.power.rate, endpoint.power.lower, endpoint.power.upper)]);
      }
      lines.push(['Any', share(c.power_any.rate, c.power_any.lower, c.power_any.upper), 'At least one rejected']);
      lines.push(['All', share(c.power_all.rate, c.power_all.lower, c.power_all.upper), 'Every one rejected']);
    }
    // A re-estimated design: its rule, the expected size, and Type I at each null scenario.
    if (Array.isArray(c.null_scenarios)) {
      lines.push(['Re-estimated', 'After ' + c.interim_per_arm + ' per arm, ' + c.initial_per_arm + ' to ' + c.max_per_arm + ' per arm',
        'Expected size ' + Math.round(numberValue(c.expected_sample_size)) + ' participants']);
      for (const scenario of c.null_scenarios) {
        lines.push(['Type I at SD ' + short(scenario.sd), share(scenario.typeI, scenario.typeI_lower, scenario.typeI_upper),
          'Expected size ' + Math.round(numberValue(scenario.expected_sample_size))]);
      }
    }
    // A design with looks: how often each look stopped the trial, and the expected size.
    if (Array.isArray(c.looks)) {
      lines.push(['Looks', c.looks.map(look => look.n_control + ' and ' + look.n_treatment + ': stops ' + percent(look.stop)).join('; '),
        'Under the null: ' + c.looks.map(look => percent(look.stop_null)).join(', ')]);
      lines.push(['Expected size', Math.round(numberValue(c.expected_sample_size)) + ' participants',
        'Under the null: ' + Math.round(numberValue(c.expected_sample_size_null))]);
    }
    lines.push(['Runs', Number(c.runs).toLocaleString('en') + ' per estimate, seed ' + c.seed]);
    if (c.scenario) lines.push(['Scenario', c.scenario.replace(/^./, ch => ch.toUpperCase())]);
    if (c.candidates_evaluated !== undefined) lines.push(['Searched', plural(c.candidates_evaluated, 'size') + ', ' + plural(c.confirmations || 0, 'confirmation run')]);
    return lines;
  }
  if (!c.power && c.candidates_evaluated !== undefined && c.runs !== undefined) {
    lines.push(['Searched', plural(c.candidates_evaluated, 'size') + ' with ' + Number(c.runs).toLocaleString('en') + ' runs each, seed ' + c.seed]);
    return lines;
  }
  if (c.power) lines.push(['Power', decimal(c.power) + (c.minimum_power ? ', target ' + decimal(c.minimum_power) : ''), exactTitle(c.power)]);
  if (c.typeI) lines.push(['Type I', decimal(c.typeI) + (c.maximum_typeI ? ', at most ' + decimal(c.maximum_typeI) : ''), exactTitle(c.typeI)]);
  if (c.critical_value !== undefined) lines.push(['Rejects at', String(c.critical_value) + ' or more']);
  if (c.candidates_evaluated !== undefined) lines.push(['Searched', plural(c.candidates_evaluated, 'candidate')]);
  return lines;
}

// A gold medal for checks Lean certified: a scalloped rosette, a coin with a darker rim
// underneath like the blocks, a small laurel, a tick and two ribbon tails.
export function certStamp(cls = 'cert-medal') {
  const svg = svgNode('svg', {viewBox: '0 0 52 60', class: cls, 'aria-hidden': 'true'});
  const tails = svgNode('g', {class: 'medal-ribbon'});
  tails.append(
    svgNode('path', {d: 'M18 32 L26 36 L20.5 57 L15.8 52 L10.5 54.5 Z'}),
    svgNode('path', {d: 'M34 32 L26 36 L31.5 57 L36.2 52 L41.5 54.5 Z'}),
    svgNode('path', {d: 'M21.5 36 L17.6 51.5 M30.5 36 L34.4 51.5', class: 'medal-ribbon-line'}));
  // A rosette of 28 points, alternately out and in, with rounded joins: a scalloped rim.
  const points = [];
  for (let i = 0; i < 28; i++) {
    const angle = (i / 28) * Math.PI * 2;
    const radius = i % 2 ? 17.6 : 19.6;
    points.push((26 + radius * Math.cos(angle)).toFixed(2) + ',' + (23 + radius * Math.sin(angle)).toFixed(2));
  }
  // Three leaves on each side of the tick, on a circle around it, each along the circle.
  const leaves = svgNode('g', {class: 'medal-laurel'});
  for (const degrees of [150, 180, 210, 30, 0, -30]) {
    const a = degrees * Math.PI / 180;
    const cx = (26 + 9.6 * Math.cos(a)).toFixed(2), cy = (23 - 9.6 * Math.sin(a)).toFixed(2);
    leaves.append(svgNode('ellipse', {cx, cy, rx: 2.5, ry: 1.15, transform: `rotate(${90 - degrees} ${cx} ${cy})`}));
  }
  svg.append(
    tails,
    svgNode('polygon', {points: points.join(' '), class: 'medal-rosette'}),
    svgNode('circle', {cx: 26, cy: 24.6, r: 14, class: 'medal-rim'}),
    svgNode('circle', {cx: 26, cy: 23, r: 14, class: 'medal-coin'}),
    svgNode('circle', {cx: 26, cy: 23, r: 11.4, class: 'medal-ring'}),
    leaves,
    svgNode('path', {d: 'M21 23.4 L24.6 27 L31.4 19.6', class: 'medal-tick'}),
    svgNode('path', {d: 'M16.6 18.6 A11 11 0 0 1 21.4 13.6', class: 'medal-shine'}));
  return svg;
}

// Simulated power at every size a search tried: the estimate, its 95% band, the target and
// the size chosen. One series, so no legend; hover for any size, or open the table.
const svgNode = (tag, attributes = {}, text) => {
  const node = document.createElementNS(SVG, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  if (text !== undefined) node.textContent = text;
  return node;
};
export function powerCurve(c) {
  const curve = c?.curve || [];
  if (curve.length < 2) return null;
  const W = 320, H = 156, L = 34, R = 12, T = 12, B = 24;
  const sizes = curve.map(point => point.n_control);
  const first = Math.min(...sizes), last = Math.max(...sizes);
  const x = n => L + (n - first) / (last - first || 1) * (W - L - R);
  const y = share => T + (1 - share) * (H - T - B);
  const target = numberValue(c.minimum_power);
  const chosen = c.power_target_met ? c.n_control : null;
  const box = el('figure', 'power-curve');
  box.dataset.tone = 'simulated';
  const caption = el('figcaption', 'curve-title', 'Simulated power by size');
  const svg = svgNode('svg', {viewBox: `0 0 ${W} ${H}`, role: 'img', class: 'curve-plot',
    'aria-label': 'Simulated power from ' + first + ' to ' + last + ' per arm' + (chosen ? '; ' + chosen + ' per arm reaches the target' : '; no size reaches the target')});
  for (const share of [0, 0.5, 1]) {
    svg.append(svgNode('line', {x1: L, x2: W - R, y1: y(share), y2: y(share), class: 'curve-grid'}));
    svg.append(svgNode('text', {x: L - 6, y: y(share) + 3.5, 'text-anchor': 'end', class: 'curve-label'}, share * 100 + '%'));
  }
  const band = curve.map(p => `${x(p.n_control)},${y(p.upper)}`).concat(curve.slice().reverse().map(p => `${x(p.n_control)},${y(p.lower)}`));
  svg.append(svgNode('polygon', {points: band.join(' '), class: 'curve-band'}));
  svg.append(svgNode('polyline', {points: curve.map(p => `${x(p.n_control)},${y(p.power)}`).join(' '), class: 'curve-line'}));
  if (Number.isFinite(target)) {
    svg.append(svgNode('line', {x1: L, x2: W - R, y1: y(target), y2: y(target), class: 'curve-target'}));
    svg.append(svgNode('text', {x: L + 4, y: y(target) - 5, class: 'curve-label'}, 'target ' + percent(target)));
  }
  // The chosen size is named on the axis, with a drop line to its point.
  const point = chosen === null ? null : curve.find(p => p.n_control === chosen);
  for (const n of [first, last]) {
    if (point && n === chosen) continue;
    if (point && Math.abs(x(n) - x(chosen)) < 40) continue;
    svg.append(svgNode('text', {x: x(n), y: H - 6, 'text-anchor': n === first ? 'start' : 'end', class: 'curve-label'}, String(n)));
  }
  if (point) {
    const atEnd = x(chosen) > W - R - 40;
    svg.append(svgNode('line', {x1: x(chosen), x2: x(chosen), y1: y(point.power), y2: H - B, class: 'curve-drop'}));
    svg.append(svgNode('circle', {cx: x(chosen), cy: y(point.power), r: 4.5, class: 'curve-chosen'}));
    svg.append(svgNode('text', {x: x(chosen), y: H - 6, 'text-anchor': atEnd ? 'end' : 'middle', class: 'curve-label strong'}, chosen + ' per arm'));
  }
  // The crosshair snaps to the nearest size tried.
  const cross = svgNode('line', {y1: T, y2: H - B, class: 'curve-cross', visibility: 'hidden'});
  const dot = svgNode('circle', {r: 4, class: 'curve-hover', visibility: 'hidden'});
  svg.append(cross, dot);
  const tip = el('div', 'curve-tip');
  tip.hidden = true;
  const hide = () => { tip.hidden = true; cross.setAttribute('visibility', 'hidden'); dot.setAttribute('visibility', 'hidden'); };
  svg.addEventListener('pointermove', event => {
    const rect = svg.getBoundingClientRect();
    if (!rect.width) return;
    const at = first + ((event.clientX - rect.left) / rect.width * W - L) / (W - L - R) * (last - first);
    const point = curve.reduce((best, p) => Math.abs(p.n_control - at) < Math.abs(best.n_control - at) ? p : best);
    cross.setAttribute('x1', x(point.n_control));
    cross.setAttribute('x2', x(point.n_control));
    dot.setAttribute('cx', x(point.n_control));
    dot.setAttribute('cy', y(point.power));
    cross.setAttribute('visibility', 'visible');
    dot.setAttribute('visibility', 'visible');
    tip.replaceChildren(el('strong', '', percent(point.power)), el('span', '', ' ' + percent(point.lower).replace('%', '') + '–' + percent(point.upper)),
      el('span', 'curve-tip-n', sizeText(point)));
    tip.hidden = false;
    const left = x(point.n_control) / W * rect.width;
    tip.style.left = Math.min(Math.max(left, 60), rect.width - 60) + 'px';
  });
  svg.addEventListener('pointerleave', hide);
  // The same numbers as a table, for screen readers and exact reading.
  const table = el('details', 'curve-table');
  table.append(el('summary', '', 'Table'));
  const grid = el('table');
  const head = el('tr');
  for (const label of ['Per arm', 'Power', '95% interval']) head.append(el('th', '', label));
  grid.append(head);
  for (const point of curve) {
    const row = el('tr');
    row.append(el('td', '', sizeText(point)), el('td', '', percent(point.power)), el('td', '', percent(point.lower).replace('%', '') + '–' + percent(point.upper)));
    if (point.n_control === chosen) row.className = 'chosen';
    grid.append(row);
  }
  table.append(grid);
  box.append(caption, svg, tip, table);
  return box;
}

// Scroll a panel to show a node without scrolling the page itself.
export function scrollInside(container, node, block = 'nearest') {
  if (!container || !node?.getBoundingClientRect) return;
  const view = container.getBoundingClientRect();
  const rect = node.getBoundingClientRect();
  let top = container.scrollTop;
  let left = container.scrollLeft;
  if (block === 'center') top += rect.top - view.top - (view.height - rect.height) / 2;
  else if (block === 'start' || rect.height > view.height - 24 || rect.top < view.top + 12) top += rect.top - view.top - 12;
  else if (rect.bottom > view.bottom - 12) top += rect.bottom - view.bottom + 12;
  if (rect.left < view.left + 12) left += rect.left - view.left - 12;
  else if (rect.right > view.right - 12) left += Math.min(rect.right - view.right + 12, rect.left - view.left - 12);
  if (container.scrollTo) container.scrollTo({top: Math.max(0, top), left: Math.max(0, left), behavior: 'smooth'});
  else { container.scrollTop = top; container.scrollLeft = left; }
}

// Suggested fixes for a contract mismatch. Every option keeps the declared null.
export function fixBox(found, done) {
  const box = el('div', 'fix-box');
  box.append(el('strong', 'fix-title', 'Ways to fix'), el('p', 'fix-summary', found.summary));
  if (found.empty) box.append(el('p', 'fix-summary', found.empty));
  for (const fix of found.fixes) {
    const item = button('', () => { done?.(); fix.apply(); }, 'fix-option');
    item.dataset.family = fix.family;
    const head = el('span', 'fix-label');
    head.append(icon('restore'), el('span', '', fix.label));
    if (fix.tier) head.append(el('span', 'tier tier-' + fix.tier, fix.tier));
    item.append(head);
    if (fix.note) item.append(el('span', 'fix-note', fix.note));
    box.append(item);
  }
  box.append(el('p', 'fix-foot', 'Each option keeps your declared null. Changing the null would change the question, so it is not offered.'));
  return box;
}
