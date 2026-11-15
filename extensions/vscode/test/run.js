const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { runTests } = require('@vscode/test-electron');

const root = path.resolve(__dirname, '../../..');
const localCode = [
  path.join(os.homedir(), 'Applications/Visual Studio Code.app/Contents/MacOS/Code'),
  '/Applications/Visual Studio Code.app/Contents/MacOS/Code'
].find(file => fs.existsSync(file));
const profile = fs.mkdtempSync(path.join(os.tmpdir(), 'statproof-vscode-test-'));
runTests({
  vscodeExecutablePath: process.env.VSCODE_EXECUTABLE_PATH || localCode,
  extensionDevelopmentPath: path.resolve(__dirname, '..'),
  extensionTestsPath: path.join(__dirname, 'suite.js'),
  extensionTestsEnv: { STATPROOF_TEST_ROOT: root },
  launchArgs: [root, '--disable-extensions', '--disable-workspace-trust',
    '--skip-welcome', '--skip-release-notes', '--user-data-dir=' + profile]
}).catch(error => { console.error(error); process.exitCode = 1; });
