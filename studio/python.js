// Start StatClaim inside Pyodide and answer the studio's API with it. The web studio's
// worker uses this in the browser, and the site check uses it in Node, so what is tested is
// what is published. `read(path)` returns the bytes of a file of the built site.
export async function startStatClaim(loadPyodide, {indexURL, read}) {
  const pyodide = await loadPyodide({indexURL});
  const text = async path => new TextDecoder().decode(await read(path));
  const manifest = JSON.parse(await text('python/manifest.json'));
  // StatClaim as built from this commit, then the studio's API beside it.
  const purelib = pyodide.runPython("import sysconfig; sysconfig.get_paths()['purelib']");
  pyodide.unpackArchive(await read('python/' + manifest.wheel), 'wheel', {extractDir: purelib});
  pyodide.FS.mkdirTree('/studio');
  pyodide.FS.writeFile('/studio/api.py', await read('python/api.py'));
  const handle = pyodide.runPython([
    'import sys',
    "sys.path.insert(0, '/studio')",
    'import api',
    'def answer(method, path, body):',
    '    return list(api.handle_json(method, path, body, api.BROWSER))',
    'answer',
  ].join('\n'));
  // One request: the method, the endpoint's name and the JSON body; a status and JSON text back.
  return (method, path, body = '') => {
    const result = handle(method, path, body);
    const [status, json] = result.toJs();
    result.destroy();
    return {status, body: json};
  };
}
