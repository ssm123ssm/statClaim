const vscode = require('vscode');
const path = require('node:path');
const fs = require('node:fs');
const { spawn } = require('node:child_process');
const { createHash } = require('node:crypto');
const { LanguageClient } = require('vscode-languageclient/node');

const hash = text => createHash('sha256').update(text, 'utf8').digest('hex');
let client;
const activeChecks = new Map();

async function activate(context) {
  const config = vscode.workspace.getConfiguration('statproof');
  const uv = config.get('uvPath', 'uv');
  const roots = (vscode.workspace.workspaceFolders || []).map(folder => folder.uri.fsPath);
  const project = config.get('projectPath') || roots.find(root =>
    fs.existsSync(path.join(root, 'src', 'statproof', 'language.py'))
  ) || path.resolve(context.extensionPath, '../..');
  const output = vscode.window.createOutputChannel('StatProof', { log: true });
  const statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 20);
  const states = new Map();
  let generation = 0;
  function refresh() {
    const document = vscode.window.activeTextEditor?.document;
    if (!document || document.languageId !== 'statproof') { statusBar.hide(); return; }
    const state = states.get(document.uri.toString());
    statusBar.text = 'StatProof: ' + (state
      ? `${state.status} (v${state.version})` : 'not verified');
    statusBar.tooltip = state
      ? `Checked snapshot v${state.version}, SHA-256 ${state.sha256}. ${state.stale ? 'Source has changed; run verification again.' : ''}`
      : 'Editing checks types and requirements only. Run verification explicitly.';
    statusBar.command = 'statproof.verifyFile';
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
  context.subscriptions.push(vscode.commands.registerCommand('statproof.verifyFile', async () => {
    const document = vscode.window.activeTextEditor?.document;
    if (!document || document.languageId !== 'statproof' || document.uri.scheme !== 'file') {
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
    const child = spawn(uv, ['run', '--locked', 'statproof', 'check', document.uri.fsPath,
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
        states.set(key, state);
        output.appendLine(`Result: ${state.status}; checked version ${version}, exit ${code}.`);
        refresh();
        resolve({ ...state, report });
      }
      child.on('error', error => finish(error, null));
      child.on('close', code => finish(null, code));
    });
  }));
  client = new LanguageClient('statproof', 'StatProof', {
    command: uv, args: ['run', '--locked', 'statproof', 'lsp'], options: { cwd: project }
  }, {
    documentSelector: [{ scheme: 'file', language: 'statproof' }, { scheme: 'untitled', language: 'statproof' }],
    outputChannel: output
  });
  await client.start();
  context.subscriptions.push(vscode.commands.registerCommand('statproof.restartServer', async () => {
    generation += 1;
    for (const [key, state] of states) states.set(key, { ...state, status: 'stale', stale: true });
    refresh();
    await client.restart();
  }));
  refresh();
  return { ready: true, project, getVerificationState: uri => states.get(uri.toString()) };
}

async function deactivate() {
  for (const child of activeChecks.values()) child.kill('SIGTERM');
  activeChecks.clear();
  if (client) await client.stop();
}

module.exports = { activate, deactivate };
