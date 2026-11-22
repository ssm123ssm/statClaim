const vscode = require('vscode');
const path = require('node:path');
const fs = require('node:fs');
const { spawn } = require('node:child_process');
const { createHash } = require('node:crypto');
const { LanguageClient } = require('vscode-languageclient/node');
const { ClaimsView } = require('./claims-view');

const hash = text => createHash('sha256').update(text, 'utf8').digest('hex');
let client;
const activeChecks = new Map();

async function activate(context) {
  const config = vscode.workspace.getConfiguration('statclaim');
  const uv = config.get('uvPath', 'uv');
  const roots = (vscode.workspace.workspaceFolders || []).map(folder => folder.uri.fsPath);
  const project = config.get('projectPath') || roots.find(root =>
    fs.existsSync(path.join(root, 'src', 'statclaim', 'language', '__init__.py'))
  ) || path.resolve(context.extensionPath, '../..');
  const output = vscode.window.createOutputChannel('StatClaim', { log: true });
  const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 20);
  const states = new Map();
  let generation = 0;
  let claimsView;
  function refresh() {
    claimsView?.schedule();
    const document = vscode.window.activeTextEditor?.document;
    if (!document || document.languageId !== 'statclaim') { statusBar.hide(); return; }
    const state = states.get(document.uri.toString());
    statusBar.text = 'StatClaim: ' + (state
      ? `${state.status} (v${state.version})` : 'not verified');
    statusBar.tooltip = state
      ? `Checked snapshot v${state.version}, SHA-256 ${state.sha256}. ${state.stale ? 'Source has changed; run verification again.' : ''}`
      : 'Editing checks types and requirements only. Run verification explicitly.';
    statusBar.command = 'statclaim.verifyFile';
    statusBar.show();
  }
  context.subscriptions.push(output, statusBar,
    vscode.window.onDidChangeActiveTextEditor(refresh),
    vscode.workspace.onDidCloseTextDocument(document => states.delete(document.uri.toString())),
    vscode.workspace.onDidChangeTextDocument(event => {
      const key = event.document.uri.toString();
      const state = states.get(key);
      if (state && event.contentChanges.length) {
        states.set(key, { ...state, status: 'stale', stale: true });
        refresh();
      }
    })
  );
  context.subscriptions.push(vscode.commands.registerCommand('statclaim.verifyFile', async () => {
    const document = vscode.window.activeTextEditor?.document;
    if (!document || document.languageId !== 'statclaim' || document.uri.scheme !== 'file') {
      vscode.window.showInformationMessage('Open a saved .stat file to verify.');
      return;
    }
    const key = document.uri.toString();
    if (activeChecks.has(key)) {
      vscode.window.showInformationMessage('Verification for this file is already running.');
      return;
    }
    if (!await document.save()) return;
    const version = document.version;
    const sha256 = hash(document.getText());
    const checkedGeneration = generation;
    states.set(key, { status: 'checking', version, sha256, stale: false });
    refresh();
    output.show(true);
    output.appendLine(`Checking ${document.fileName}, version ${version}, SHA-256 ${sha256}`);
    const child = spawn(uv, ['run', '--locked', 'statclaim', 'check', document.uri.fsPath,
      '--project', project, '--json'], { cwd: project, shell: false });
    activeChecks.set(key, child);
    return await new Promise(resolve => {
      let stdout = '';
      let finished = false;
      child.stdout.setEncoding('utf8');
      child.stderr.setEncoding('utf8');
      child.stdout.on('data', chunk => { stdout += chunk; });
      child.stderr.on('data', chunk => output.append(chunk));
      function finish(error, code) {
        if (finished) return;
        finished = true;
        activeChecks.delete(key);
        let report;
        let status = 'backend error';
        try {
          if (error) throw error;
          report = JSON.parse(stdout);
          status = report.status;
          output.appendLine(JSON.stringify(report, null, 2));
        } catch (failure) {
          output.appendLine(String(failure));
          if (stdout) output.appendLine(stdout);
        }
        const stale = Boolean(generation !== checkedGeneration || document.isClosed || document.version !== version ||
          hash(document.getText()) !== sha256 || (report && (
            report.source?.sha256 !== sha256 || report.status === 'stale_source')));
        const state = { status: stale ? 'stale' : status, version, sha256, stale };
        states.set(key, { ...state, report });
        output.appendLine(`Result: ${state.status}; checked version ${version}, exit ${code}.`);
        refresh();
        resolve({ ...state, report });
      }
      child.on('error', error => finish(error, null));
      child.on('close', code => finish(null, code));
    });
  }));
  client = new LanguageClient('statclaim', 'StatClaim', {
    command: uv, args: ['run', '--locked', 'statclaim', 'lsp'], options: { cwd: project }
  }, {
    documentSelector: [{ scheme: 'file', language: 'statclaim' }, { scheme: 'untitled', language: 'statclaim' }],
    outputChannel: output
  });
  await client.start();
  claimsView = new ClaimsView(client, states, hash);
  const tree = vscode.window.createTreeView('statclaim.claims', { treeDataProvider: claimsView });
  context.subscriptions.push(claimsView, tree,
    vscode.commands.registerCommand('statclaim.showClaims', () => vscode.commands.executeCommand('statclaim.claims.focus')),
    vscode.commands.registerCommand('statclaim.revealLocation', async location => {
      const document = await vscode.workspace.openTextDocument(vscode.Uri.parse(location.uri));
      await vscode.window.showTextDocument(document, { selection: new vscode.Range(
        location.range.start.line, location.range.start.character,
        location.range.end.line, location.range.end.character) });
    })
  );
  // Explanations appear only when asked for. A passing contract shows nothing by itself.
  async function showMarkdown(method, withPosition) {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'statclaim') {
      vscode.window.showInformationMessage('Open a .stat file first.');
      return null;
    }
    const params = { textDocument: { uri: editor.document.uri.toString() } };
    if (withPosition) {
      params.position = { line: editor.selection.active.line, character: editor.selection.active.character };
    }
    const result = await client.sendRequest(method, params);
    if (!result) return null;
    const document = await vscode.workspace.openTextDocument({ language: 'markdown', content: result.markdown });
    await vscode.window.showTextDocument(document, { viewColumn: vscode.ViewColumn.Beside, preview: true, preserveFocus: true });
    return result;
  }
  context.subscriptions.push(
    vscode.commands.registerCommand('statclaim.explainContract', () => showMarkdown('statclaim/explain', true)),
    vscode.commands.registerCommand('statclaim.showImpact', () => showMarkdown('statclaim/impact', false))
  );
  context.subscriptions.push(vscode.commands.registerCommand('statclaim.restartServer', async () => {
    generation += 1;
    for (const [key, state] of states) states.set(key, { ...state, status: 'stale', stale: true });
    refresh();
    await client.restart();
    claimsView.schedule();
  }));
  refresh();
  return { ready: true, project, getVerificationState: uri => states.get(uri.toString()),
    getClaims: () => claimsView.roots };
}

async function deactivate() {
  for (const child of activeChecks.values()) child.kill('SIGTERM');
  activeChecks.clear();
  if (client) await client.stop();
}

module.exports = { activate, deactivate };
