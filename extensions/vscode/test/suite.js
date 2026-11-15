const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');

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
  const root = process.env.STATPROOF_TEST_ROOT;
  const extension = vscode.extensions.getExtension('statproof-local.statproof');
  assert.ok(extension, 'extension registered');
  const api = await extension.activate();
  assert.equal(api.ready, true);
  fs.mkdirSync(path.join(root, '.statproof'), { recursive: true });
  const directory = fs.mkdtempSync(path.join(root, '.statproof', 'ide-test-'));
  const file = path.join(directory, 'study 🧪.stat');
  const base = fs.readFileSync(path.join(root, 'examples/fisher.stat'), 'utf8');
  fs.writeFileSync(file, base.replace('alpha=1/20', 'alpha=2'));
  const document = await vscode.workspace.openTextDocument(file);
  await vscode.window.showTextDocument(document);
  assert.equal(document.languageId, 'statproof');
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
    'let validity = typeI(analysis)\nlet checked = verify(validity)');
  await replace(source);
  await until(() => diagnostics().length === 0, 'diagnostic clearing');
  const usage = source.indexOf('verify(validity)') + 'verify('.length;
  const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, document.positionAt(usage));
  assert.ok(hovers.length);
  assert.ok(hovers[0].contents.some(item => item.value.includes('Required assumptions')));
  const plan = source.indexOf('design=plan') + 'design='.length;
  const definitions = await vscode.commands.executeCommand('vscode.executeDefinitionProvider', document.uri, document.positionAt(plan));
  assert.equal(definitions[0].range.start.line, document.positionAt(source.indexOf('let plan')).line);
  console.log('PASS: hover meanings, definition lookup, and obsolete diagnostics cleared');

  const result = await vscode.commands.executeCommand('statproof.verifyFile');
  assert.equal(result.status, 'verified');
  assert.equal(result.sha256, result.report.source.sha256);
  assert.ok(result.report.values.checked.evidence.certificate.file);
  const checkedVersion = result.version;
  await replace(source + '\n# changed after verification\n');
  await until(() => api.getVerificationState(document.uri)?.status === 'stale', 'stale status');
  assert.equal(api.getVerificationState(document.uri).version, checkedVersion);
  console.log('PASS: explicit real Lean verification and stale snapshot status');

  await replace(source);
  const pending = vscode.commands.executeCommand('statproof.verifyFile');
  await until(() => api.getVerificationState(document.uri)?.status === 'checking', 'pending verification');
  await replace(source + '\n# editing during verification\n');
  const concurrent = await pending;
  assert.equal(concurrent.status, 'stale');
  assert.equal(concurrent.stale, true);
  assert.ok(concurrent.report.values.checked.evidence);
  console.log('PASS: editing during verification cannot display a current verified status');

  await vscode.commands.executeCommand('statproof.restartServer');
  assert.equal(api.getVerificationState(document.uri).status, 'stale');
  const afterRestart = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, document.positionAt(usage));
  assert.ok(afterRestart.length);
  console.log('PASS: server restart restores editor features and keeps proof status stale');

  const pendingAtRestart = vscode.commands.executeCommand('statproof.verifyFile');
  await until(() => api.getVerificationState(document.uri)?.status === 'checking', 'check before restart');
  await vscode.commands.executeCommand('statproof.restartServer');
  const restartedCheck = await pendingAtRestart;
  assert.equal(restartedCheck.status, 'stale');
  assert.equal(restartedCheck.report.status, 'verified');
  console.log('PASS: a server restart during verification cannot restore a current proof status');

  await document.save();
  fs.writeFileSync(path.join(directory, 'test-result.json'), JSON.stringify({ passed: true, version: checkedVersion, certificate: result.report.values.checked.evidence.certificate }, null, 2));
  console.log('StatProof editor integration passed. Result: ' + directory);
}

module.exports = { run: async () => {
  try { await run(); }
  catch (error) { console.error(error.stack || error); throw error; }
} };
