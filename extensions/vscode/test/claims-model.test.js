const assert = require('node:assert/strict');
const test = require('node:test');
const { buildClaimsTree } = require('../claims-model');

const claim = { kind: 'typeI', subject_name: 'analysis', subject: { alpha: '1/20' } };
const inspection = { uri: 'file:///study.stat', version: 2, status: 'elaborated', diagnostics: [], claims: [{
  names: ['validity'], kind: 'typeI', claim, description: 'Uniform Type I bound', assumptions: ['Declared model'],
  requirements: [], range: { start: { line: 1, character: 0 }, end: { line: 1, character: 10 } },
  requests: [{ request_id: 1, operation: 'verify', names: ['checked'], requirements: [] }]
}] };
const evidence = { certificate: { certificate_id: 'certificate', file: '/certificate.json', sha256: 'hash' },
  established_properties: ['Bound checked'], required_assumptions: ['Declared model'] };
const request = { request_id: 1, operation: 'verify', status: 'verified', value: { status: 'verified', claim, evidence } };
const state = { version: 2, sha256: 'source', stale: false,
  report: { source: { sha256: 'source' }, requests: [request] } };
const live = { version: 2, sha256: 'source' };
const labels = nodes => nodes.flatMap(node => [node.label, ...labels(node.children || [])]);

test('compiler inspection alone never supplies checked evidence', () => {
  const tree = labels(buildClaimsTree(inspection, undefined, live));
  assert.ok(tree.includes('verify #1: not executed'));
  assert.ok(!tree.includes('Checked evidence'));
  assert.ok(tree.includes('No known blocker; this is not a proof'));
});

test('only a matching execution snapshot exposes current evidence and checked assumptions', () => {
  const tree = labels(buildClaimsTree(inspection, state, live));
  assert.ok(tree.includes('verify #1: verified'));
  assert.ok(tree.includes('Checked evidence'));
  assert.ok(tree.includes('Required assumptions — not established by this proof'));
});

for (const [index, changed] of [{ ...state, stale: true }, { ...state, version: 1 }, { ...state, sha256: 'old' },
  { ...state, report: { ...state.report, source: { sha256: 'old' } } }].entries()) {
  test('stale or mismatched execution is historical only, case ' + index, () => {
    const tree = buildClaimsTree(inspection, changed, live);
    const current = labels(tree.filter(node => !node.label.startsWith('Previous execution')));
    assert.ok(!current.includes('Checked evidence'));
    assert.ok(!current.includes('verify #1: verified'));
    assert.ok(labels(tree).includes('Historical evidence — previous snapshot only'));
  });
}

test('backend errors and unmet requirements never gain evidence', () => {
  for (const status of ['backend_error', 'unresolved_obligation']) {
    const failed = { ...state, report: { ...state.report, requests: [{ ...request,
      value: { ...request.value, status, evidence: null } }] } };
    assert.ok(!labels(buildClaimsTree(inspection, failed, live)).includes('Checked evidence'));
  }
});

test('a mismatched claim cannot borrow another claim certificate even with a matching source hash', () => {
  const wrong = { ...state, report: { ...state.report, requests: [{ ...request,
    value: { ...request.value, claim: { ...claim, kind: 'result' } } }] } };
  assert.ok(!labels(buildClaimsTree(inspection, wrong, live)).includes('Checked evidence'));
});
