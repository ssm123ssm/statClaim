// Where the studio's API runs. On this machine, studio/server.py answers over HTTP. In the web
// studio (the page carries <meta name="statclaim-backend" content="browser">), StatClaim runs
// in this browser, in worker.js, and the answers that never change are files beside the page.
// Both answer with api.py, so the page cannot tell them apart except by what Lean can do.
export const where = document.querySelector('meta[name="statclaim-backend"]')?.content === 'browser' ? 'browser' : 'server';

let worker = null;
let state = 'idle';
let failure = '';
const listeners = new Set();
const queue = [];
let busy = null;
let next = 0;

function setState(value, detail = '') {
  state = value;
  failure = detail;
  for (const listener of listeners) listener(state, failure);
}
// Called with 'starting', 'ready' or 'failed' as StatClaim starts in the browser.
export function onState(listener) {
  listeners.add(listener);
  listener(state, failure);
  return () => listeners.delete(listener);
}

// Starts StatClaim in the browser early, so it is ready by the first edit.
export function prepare() {
  if (where !== 'browser' || worker) return;
  setState('starting');
  worker = new Worker(new URL('worker.js', import.meta.url), {type: 'module'});
  worker.onmessage = ({data}) => {
    if (data.ready) return setState('ready');
    if (data.failed) return setState('failed', data.failed);
    if (busy?.id === data.id) {
      busy.resolve(data);
      busy = null;
      pump();
    }
  };
  worker.onerror = event => {
    setState('failed', event.message || 'the worker stopped');
    busy?.resolve({status: 503, body: JSON.stringify({error: 'StatClaim stopped in this browser. Reload the page.'})});
    busy = null;
  };
}

// One request at a time: a request cancelled while it waits, such as a stale compile while
// typing, is dropped before StatClaim spends time on it.
function pump() {
  while (!busy && queue.length) {
    const item = queue.shift();
    if (item.signal?.aborted) { item.reject(new DOMException('Aborted', 'AbortError')); continue; }
    busy = item;
    worker.postMessage({id: item.id, method: 'POST', path: item.path, body: item.body});
  }
}

// The same contract as fetch('/api/' + path, options): a Response.
export async function request(path, options = {}) {
  if (where === 'server') return fetch('/api/' + path, options);
  if (!options.method || options.method === 'GET') {
    return fetch(new URL('api/' + path + '.json', document.baseURI), {signal: options.signal});
  }
  prepare();
  if (options.signal?.aborted) throw new DOMException('Aborted', 'AbortError');
  const answer = await new Promise((resolve, reject) => {
    queue.push({id: ++next, path, body: options.body || '', signal: options.signal, resolve, reject});
    pump();
  });
  if (options.signal?.aborted) throw new DOMException('Aborted', 'AbortError');
  return new Response(answer.body, {status: answer.status, headers: {'Content-Type': 'application/json'}});
}
