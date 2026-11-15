const vscode = require('vscode');
const { buildClaimsTree } = require('./claims-model');

class ClaimsView {
  constructor(client, states, hash) {
    this.client = client;
    this.states = states;
    this.hash = hash;
    this.roots = buildClaimsTree(null);
    this.sequence = 0;
    this.changed = new vscode.EventEmitter();
    this.onDidChangeTreeData = this.changed.event;
    this.disposables = [
      vscode.window.onDidChangeActiveTextEditor(() => this.schedule()),
      vscode.workspace.onDidChangeTextDocument(event => {
        if (event.contentChanges.length && event.document === this.document) this.schedule();
      }),
      vscode.workspace.onDidCloseTextDocument(document => {
        if (document === this.document) { this.document = undefined; this.schedule(); }
      })
    ];
  }
  getChildren(element) { return element ? element.children || [] : this.roots; }
  getTreeItem(node) {
    const item = new vscode.TreeItem(node.label, node.children?.length
      ? vscode.TreeItemCollapsibleState.Collapsed : vscode.TreeItemCollapsibleState.None);
    item.tooltip = node.label;
    item.description = node.description;
    if (node.location?.range) item.command = { command: 'statproof.revealLocation', title: 'Show declaration', arguments: [node.location] };
    if (node.certificate) item.command = { command: 'vscode.open', title: 'Open certificate', arguments: [vscode.Uri.file(node.certificate)] };
    return item;
  }
  schedule() {
    clearTimeout(this.timer);
    const sequence = ++this.sequence;
    const active = vscode.window.activeTextEditor?.document;
    if (active?.languageId === 'statproof') this.document = active;
    const document = this.document;
    if (!document || document.isClosed) {
      this.roots = buildClaimsTree(null);
      this.changed.fire();
      return;
    }
    const live = { version: document.version, sha256: this.hash(document.getText()) };
    const uri = document.uri.toString();
    const inspection = this.inspection?.uri === uri && this.inspection.version === live.version
      ? this.inspection : { uri, version: live.version, status: 'analyzing', claims: [], diagnostics: [] };
    this.roots = buildClaimsTree(inspection, this.states.get(uri), live);
    this.changed.fire();
    this.timer = setTimeout(async () => {
      try {
        const result = await this.client.sendRequest('statproof/inspect', { textDocument: { uri }, version: live.version });
        if (sequence !== this.sequence || document.isClosed || document.version !== live.version) return;
        if (!result || result.version !== live.version) { this.schedule(); return; }
        this.inspection = result;
        this.roots = buildClaimsTree(result, this.states.get(uri), live);
        this.changed.fire();
      } catch (error) {
        if (sequence === this.sequence) {
          this.roots = [ { label: 'Claims unavailable: ' + error.message } ];
          this.changed.fire();
        }
      }
    }, 60);
  }
  dispose() {
    clearTimeout(this.timer);
    this.sequence += 1;
    this.disposables.forEach(item => item.dispose());
    this.changed.dispose();
  }
}

module.exports = { ClaimsView };
