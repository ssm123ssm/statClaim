// Pure presentation model: only matching explicit execution snapshots can add
// current evidence. Compiler inspection data never supplies proof results.
const leaf = (label, extra = {}) => ({ label, ...extra });
const group = (label, children, extra = {}) => ({ label, children, ...extra });
// Mirrors GRADES and SCOPES in methods/core.py.
const GRADES = {
  proved: 'proved in Lean',
  conditional: "combination proved in Lean; the members' own guarantees are assumed",
  cited: 'cited from the literature; not machine-checked',
  simulated: 'estimated by simulation; not a proof',
  declared: 'declared by the author; not checked and not cited'
};
const SCOPES = { finite_sample: 'finite-sample bound', asymptotic: 'large-sample approximation' };
// Mirrors SCOPE_NOTE in reference.py: what any evidence covers, and what it cannot.
const SCOPE_NOTE = 'Concerns the study as declared, under the listed assumptions; ' +
  'says nothing about how the study is run';

function evidenceNodes(value, historical = false) {
  const evidence = value?.evidence;
  if (['cited', 'declared'].includes(value?.status) && evidence) {
    const title = value.status === 'declared'
      ? 'Declared by the author — not checked and not cited' : 'Cited guarantee — not machine-checked';
    return [group(historical ? 'Historical unchecked guarantee — previous snapshot only' : title, [
      leaf(`Evidence grade: ${GRADES[evidence.grade] || 'unknown'}`),
      leaf(SCOPE_NOTE),
      ...(evidence.method ? [leaf(`Method: ${evidence.method.title} (version ${evidence.method.version})`)] : []),
      group('Cited properties', evidence.established_properties.map(text => leaf(text))),
      group('Required assumptions — declared by this file, or assumed',
        (evidence.assumptions || []).map(item => leaf(`${item.text} (${item.status})`))),
      group('References', evidence.references.map(text => leaf(text)))
    ])];
  }
  if (!['verified', 'conditional'].includes(value?.status) || !evidence) return [leaf('No checked evidence')];
  const certificate = evidence.certificate;
  const title = value.status === 'conditional'
    ? 'Conditional evidence — combination checked, members assumed' : 'Checked evidence';
  return [group(historical ? 'Historical evidence — previous snapshot only' : title, [
    leaf(`Evidence grade: ${GRADES[evidence.grade] || 'unknown'}`),
    leaf(SCOPE_NOTE),
    leaf(`Certificate: ${certificate.certificate_id}`, { certificate: certificate.file }),
    leaf(`Certificate SHA-256: ${certificate.sha256}`),
    group('Established properties', evidence.established_properties.map(text => leaf(text))),
    group('Required assumptions — not established by this proof',
      evidence.required_assumptions.map(text => leaf(text)))
  ])];
}

function resultNode(request, historical = false) {
  const value = request.value;
  const status = value?.status || request.status;
  const children = request.operation === 'verify' ? evidenceNodes(value, historical) : [
    leaf('Numerical calculation only; no formal evidence'),
    ...(value?.calculation ? [leaf(`p-value: ${value.calculation.p_value.fraction}`)] : []),
    leaf(`Decision: ${value?.decision || 'unavailable'}`)
  ];
  children.push(...(value?.diagnostics || []).map(d => leaf(`${d.code}: ${d.message}`)));
  return group(`${historical ? 'Historical ' : ''}${request.operation} #${request.request_id}: ${status}`, children);
}

function buildClaimsTree(inspection, state, live) {
  if (!inspection) return [leaf('Open a .stat file to inspect its claims')];
  const current = Boolean(state?.report && !state.stale && state.version === live.version &&
    state.sha256 === live.sha256 && state.report.source?.sha256 === live.sha256);
  const roots = [leaf(`Current source v${live.version}: ${inspection.status}`)];
  if (inspection.diagnostics.length) {
    roots.push(group('Source diagnostics', inspection.diagnostics.map(d =>
      group(`${d.code}: ${d.message}`, (d.relatedInformation || []).map(related =>
        leaf(related.message, { location: related.location })),
      { location: { uri: inspection.uri, range: d.range } }))));
  }
  for (const claim of inspection.claims) {
    const children = [leaf(claim.description),
      leaf(`Guarantee: ${SCOPES[claim.scope] || 'unknown'}`),
      group('Declared assumptions', claim.assumptions.map(text => leaf(text))),
      group('Known requirements', claim.requirements.length
        ? claim.requirements.map(d => leaf(`${d.code}: ${d.message}`, {
          location: { uri: inspection.uri, range: d.range }
        })) : [leaf('No known blocker; this is not a proof')])];
    if (!claim.requests.length) children.push(leaf('Declared claim; no operation requested'));
    for (const planned of claim.requests) {
      const actual = current && state.report.requests.find(r =>
        r.request_id === planned.request_id && JSON.stringify(r.value?.claim) === JSON.stringify(claim.claim));
      if (actual) children.push({ ...resultNode(actual), description: planned.names.join(', ') });
      else children.push(group(`${planned.operation} #${planned.request_id}: ${planned.requirements.length || inspection.status === 'invalid' ? 'blocked' : 'not executed'}`,
        [leaf('No current checked evidence')], { description: planned.names.join(', ') }));
    }
    roots.push(group(`${claim.names.join(', ') || 'Unnamed claim'} — ${claim.kind}`, children, {
      location: { uri: inspection.uri, range: claim.range }
    }));
  }
  if (state?.report && !current) {
    roots.push(group(`Previous execution — stale (v${state.version})`, [
      leaf(`Applies only to SHA-256 ${state.sha256}`),
      ...state.report.requests.map(request => resultNode(request, true))
    ]));
  }
  return roots;
}

module.exports = { buildClaimsTree };
