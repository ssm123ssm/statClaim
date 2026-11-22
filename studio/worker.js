// The web studio's worker: StatClaim runs here, off the page's thread, so the page stays
// responsive while a study compiles or a simulation runs. Requests arrive one at a time.
import { loadPyodide } from './pyodide/pyodide.mjs';
import { startStatClaim } from './python.js';

const base = new URL('./', import.meta.url);
const ready = startStatClaim(loadPyodide, {
  indexURL: new URL('pyodide/', base).href,
  read: async path => {
    const response = await fetch(new URL(path, base));
    if (!response.ok) throw Error('could not load ' + path + ' (' + response.status + ')');
    return new Uint8Array(await response.arrayBuffer());
  },
});
ready.then(() => postMessage({ready: true}), error => postMessage({failed: String(error?.message || error)}));

self.onmessage = async ({data: {id, method, path, body}}) => {
  try {
    const answer = await ready;
    postMessage({id, ...answer(method, path, body)});
  } catch (error) {
    postMessage({id, status: 503, body: JSON.stringify({error: 'StatClaim could not start in this browser: ' + (error?.message || error)})});
  }
};
