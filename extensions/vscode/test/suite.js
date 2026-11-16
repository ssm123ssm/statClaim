const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');
const labels = nodes => nodes.flatMap(node => [node.label, ...labels(node.children || [])]);

async function until(callback, description, timeout = 15000) {
  const start = Date.now();
  while (Date.now() - start < timeout) {
    const value = await callback();
    if (value) return value;
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  throw new Error('Timed out: ' + description);
}

async function run() {
  const root = process.env.STATCLAIM_TEST_ROOT;
  const extension = vscode.extensions.getExtension('statclaim-local.statclaim');
  assert.ok(extension, 'extension registered');
  const api = await extension.activate();
  assert.equal(api.ready, true);
  fs.mkdirSync(path.join(root, '.statclaim'), { recursive: true });
  const directory = fs.mkdtempSync(path.join(root, '.statclaim', 'ide-test-'));
  const file = path.join(directory, 'study 🧪.stat');
  const base = fs.readFileSync(path.join(root, 'tests/fixtures/fisher.stat'), 'utf8');
  fs.writeFileSync(file, base.replace('alpha=1/20', 'alpha=2'));
  const document = await vscode.workspace.openTextDocument(file);
  await vscode.window.showTextDocument(document);
  assert.equal(document.languageId, 'statclaim');
  const diagnostics = () => vscode.languages.getDiagnostics(document.uri);
  await until(() => diagnostics().some(d => d.code === 'domain'), 'domain diagnostic');
  console.log('PASS: .stat recognition and live diagnostics');

  async function replace(text) {
    const edit = new vscode.WorkspaceEdit();
    edit.replace(document.uri, new vscode.Range(new vscode.Position(0, 0), document.positionAt(document.getText().length)), text);
    assert.equal(await vscode.workspace.applyEdit(edit), true);
  }
  async function completion(text) {
    await replace(text);
    return await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', document.uri, document.positionAt(text.length));
  }
  let items = await completion('use tests.');
  assert.ok(items.items.some(item => item.label === 'tests.fisher'));
  const prefix = base.slice(0, base.indexOf('let analysis'));
  items = await completion(prefix + 'let analysis = fisher(');
  assert.ok(items.items.some(item => item.label === 'design'));
  items = await completion(prefix + 'let analysis = fisher(design=');
  assert.ok(items.items.some(item => item.label === 'plan'));
  assert.ok(!items.items.some(item => item.label === 'null'));
  console.log('PASS: modules, named arguments, and typed objects in incomplete input');

  const source = base.replace('verify typeI(analysis)',
    'let validity = typeI(analysis)\nlet checked = verify(validity)\n' +
    'let state = checked.status\nlet proof = checked.evidence\nlet certificate_file = proof.certificate.file\n' +
    'let reasons = checked.diagnostics');
  items = await completion(source + '\nlet more = checked.evidence.');
  assert.ok(items.items.some(item => item.label === 'certificate' && item.detail === 'Option[CertificateReference]'));
  await replace(source);
  await until(() => diagnostics().length === 0, 'valid file has no diagnostics');
  const quiet = diagnostics().length;
  const explained = await vscode.commands.executeCommand('statclaim.explainContract');
  assert.ok(explained.contracts.length >= 1 && explained.contracts.every(contract => contract.checked));
  assert.ok(explained.markdown.includes('Why it passed'));
  assert.equal(diagnostics().length, quiet, 'explaining a contract adds no diagnostics');
  const changed = await vscode.commands.executeCommand('statclaim.showImpact');
  assert.ok(changed.declarations.length >= 1);
  await vscode.window.showTextDocument(document);
  console.log('PASS: Explain Contract and Change Impact on request only');
  await until(() => diagnostics().length === 0, 'diagnostic clearing');
  const usage = source.indexOf('verify(validity)') + 'verify('.length;
  const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, document.positionAt(usage));
  assert.ok(hovers.length);
  assert.ok(hovers[0].contents.some(item => item.value.includes('Required assumptions')));
  const plan = source.indexOf('design=plan') + 'design='.length;
  const definitions = await vscode.commands.executeCommand('vscode.executeDefinitionProvider', document.uri, document.positionAt(plan));
  assert.equal(definitions[0].range.start.line, document.positionAt(source.indexOf('let plan')).line);
  console.log('PASS: hover meanings, definition lookup, and obsolete diagnostics cleared');

  const shifted = source.replace('equal_proportions(model=study)', 'proportion_difference(model=study, value=0.10)');
  await replace(shifted);
  const mismatch = await until(() => diagnostics().find(d => d.code === 'hypothesis_mismatch'), 'different-null diagnostic');
  assert.ok(mismatch.message.includes('Declared null: p_treatment - p_control = 1/10'));
  assert.ok(mismatch.message.includes('Supported null: p_treatment = p_control'));
  assert.ok(mismatch.relatedInformation.length);
  const nullHover = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri,
    document.positionAt(shifted.indexOf('null =')));
  assert.ok(nullHover[0].contents.some(item => item.value.includes('p_treatment - p_control = 1/10')));
  await until(() => labels(api.getClaims()).some(label => label.includes('hypothesis_mismatch')), 'compatibility guidance in Claims');
  assert.ok(!labels(api.getClaims()).includes('Checked evidence'));
  await replace(shifted.replace('value=0.10', 'value=0'));
  await until(() => diagnostics().length === 0, 'zero difference is compatible');
  await replace(shifted.replace('proportion_difference(', 'proportion_difference_at_most(').replace('value=0.10', 'value=0'));
  const inequality = await until(() => diagnostics().find(d => d.code === 'hypothesis_mismatch'), 'inequality remains distinct at zero');
  assert.ok(inequality.message.includes('p_treatment - p_control <= 0'));
  await replace(source);
  await until(() => diagnostics().length === 0, 'original equality restored');
  console.log('PASS: same-study null compatibility, exact meanings, declaration links, and guidance');

  await vscode.commands.executeCommand('statclaim.showClaims');
  await until(() => labels(api.getClaims()).some(label => label.includes('validity — typeI')), 'current claims view');
  assert.ok(!labels(api.getClaims()).includes('Checked evidence'));
  await replace(source.replace('fixed(', 'adaptive('));
  await until(() => labels(api.getClaims()).some(label => label.includes('sampling_scope')), 'requirements in claims view');
  assert.ok(!labels(api.getClaims()).includes('Checked evidence'));
  await replace(source);
  await until(() => !labels(api.getClaims()).some(label => label.includes('sampling_scope')), 'requirements clear after edit');
  console.log('PASS: typed field completion and live claims/requirements without verification');
  await vscode.window.showTextDocument(document);

  const result = await vscode.commands.executeCommand('statclaim.verifyFile');
  assert.equal(result.status, 'verified');
  assert.equal(result.sha256, result.report.source.sha256);
  assert.ok(result.report.values.checked.evidence.certificate.file);
  assert.equal(result.report.values.state, 'verified');
  assert.equal(result.report.values.certificate_file, result.report.values.checked.evidence.certificate.file);
  await until(() => labels(api.getClaims()).includes('Checked evidence'), 'current checked evidence in claims view');
  const checkedVersion = result.version;
  await replace(source + '\n# changed after verification\n');
  await until(() => api.getVerificationState(document.uri)?.status === 'stale', 'stale status');
  assert.equal(api.getVerificationState(document.uri).version, checkedVersion);
  await until(() => labels(api.getClaims()).includes('Historical evidence — previous snapshot only'), 'historical evidence');
  const currentNodes = api.getClaims().filter(node => !node.label.startsWith('Previous execution'));
  assert.ok(!labels(currentNodes).includes('Checked evidence'));
  console.log('PASS: explicit real Lean verification and stale snapshot status');

  await replace(source);
  const pending = vscode.commands.executeCommand('statclaim.verifyFile');
  await until(() => api.getVerificationState(document.uri)?.status === 'checking', 'pending verification');
  await replace(source + '\n# editing during verification\n');
  const concurrent = await pending;
  assert.equal(concurrent.status, 'stale');
  assert.equal(concurrent.stale, true);
  assert.ok(concurrent.report.values.checked.evidence);
  console.log('PASS: editing during verification cannot display a current verified status');

  await vscode.commands.executeCommand('statclaim.restartServer');
  assert.equal(api.getVerificationState(document.uri).status, 'stale');
  const afterRestart = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, document.positionAt(usage));
  assert.ok(afterRestart.length);
  console.log('PASS: server restart restores editor features and keeps proof status stale');

  const pendingAtRestart = vscode.commands.executeCommand('statclaim.verifyFile');
  await until(() => api.getVerificationState(document.uri)?.status === 'checking', 'check before restart');
  await vscode.commands.executeCommand('statclaim.restartServer');
  const restartedCheck = await pendingAtRestart;
  assert.equal(restartedCheck.status, 'stale');
  assert.equal(restartedCheck.report.status, 'verified');
  console.log('PASS: a server restart during verification cannot restore a current proof status');

  await replace(source.replace('fixed(', 'adaptive('));
  const blocked = await vscode.commands.executeCommand('statclaim.verifyFile');
  assert.equal(blocked.status, 'unresolved_obligation');
  assert.equal(blocked.report.backend_invoked, false);
  assert.equal(blocked.report.values.proof, null);
  assert.equal(blocked.report.values.certificate_file, null);
  assert.equal(blocked.report.values.reasons[0].code, 'sampling_scope');
  await until(() => labels(api.getClaims()).some(label => label.includes('sampling_scope')), 'failed check view');
  assert.ok(!labels(api.getClaims()).includes('Checked evidence'));
  console.log('PASS: failed checks expose projected diagnostics and no evidence in language or view');

  await document.save();
  fs.writeFileSync(path.join(directory, 'test-result.json'), JSON.stringify({ passed: true, version: checkedVersion, certificate: result.report.values.checked.evidence.certificate }, null, 2));
  console.log('StatClaim editor integration passed. Result: ' + directory);
}

module.exports = { run: async () => {
  try { await run(); }
  catch (error) { console.error(error.stack || error); throw error; }
} };
