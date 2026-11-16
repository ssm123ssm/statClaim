const assert = require('node:assert/strict');
const test = require('node:test');
const { buildClaimsTree } = require('../claims-model');

const claim = { kind: 'typeI', subject_name: 'analysis', subject: { alpha: '1/20' } };
const inspection = { uri: 'file:///study.stat', version: 2, status: 'elaborated', diagnostics: [], claims: [{
  names: ['validity'], kind: 'typeI', scope: 'finite_sample', claim, description: 'Uniform Type I bound', assumptions: ['Declared model'],
  requirements: [], range: { start: { line: 1, character: 0 }, end: { line: 1, character: 10 } },
  requests: [{ request_id: 1, operation: 'verify', names: ['checked'], requirements: [] }]
}] };
const evidence = { grade: 'proved', certificate: { certificate_id: 'certificate', file: '/certificate.json', sha256: 'hash' },
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
  assert.ok(tree.includes('Evidence grade: proved in Lean'));
  assert.ok(tree.includes('Guarantee: finite-sample bound'));
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

test('a cited guarantee is never presented as checked evidence', () => {
  const cited = { grade: 'cited', certificate: null, established_properties: ['Cited, not checked: level'],
    required_assumptions: ['Normal outcomes'],
    assumptions: [{ id: 'normal_outcomes', kind: 'distribution', text: 'Normal outcomes', status: 'assumed' }],
    method: { key: 't_test', version: 1, title: 'Pooled t-test' }, references: ['Student (1908)'] };
  const citedState = { ...state, report: { source: { sha256: 'source' }, requests: [
    { request_id: 1, operation: 'verify', status: 'cited', value: { status: 'cited', claim, evidence: cited } }] } };
  const tree = labels(buildClaimsTree(inspection, citedState, live));
  assert.ok(tree.includes('verify #1: cited'));
  assert.ok(tree.includes('Cited guarantee — not machine-checked'));
  assert.ok(tree.includes('Evidence grade: cited from the literature; not machine-checked'));
  assert.ok(tree.includes('Student (1908)'));
  assert.ok(tree.includes('Normal outcomes (assumed)'));
  assert.ok(tree.includes('Method: Pooled t-test (version 1)'));
  assert.ok(!tree.includes('Checked evidence'));
});
