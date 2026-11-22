// Check the built web studio as a browser would run it, in Node: StatClaim starts in Pyodide
// from the site's own files, through the worker's code, and answers every example and lesson
// as CPython does. Run by make site-check:
//   node studio/tests/site.check.mjs dist/studio-site dist/studio-reference.json
import { existsSync, readFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { startStatClaim } from '../python.js';

const [site, referenceFile] = process.argv.slice(2).map(path => resolve(path));
const problems = [];
const problem = text => { if (problems.length < 60) problems.push(text); };

// Numbers agree to 1e-9; anything else exactly. Platforms may differ in the last digit of a
// floating-point function, never in a decision, a status or an exact fraction.
const NUMBER = /^-?\d+\.\d+(e[-+]?\d+)?$/i;
function compare(got, want, where) {
  if (typeof got === 'number' && typeof want === 'number') {
    if (Math.abs(got - want) > 1e-9 * Math.max(1, Math.abs(want))) problem(`${where}: ${got} != ${want}`);
  } else if (typeof got === 'string' && typeof want === 'string' && NUMBER.test(got) && NUMBER.test(want)) {
    compare(Number(got), Number(want), where);
  } else if (Array.isArray(got) && Array.isArray(want)) {
    if (got.length !== want.length) return problem(`${where}: ${got.length} items, expected ${want.length}`);
    got.forEach((item, i) => compare(item, want[i], `${where}[${i}]`));
  } else if (got && want && typeof got === 'object' && typeof want === 'object') {
    const keys = new Set([...Object.keys(got), ...Object.keys(want)]);
    for (const key of keys) compare(got[key], want[key], `${where}.${key}`);
  } else if (got !== want) {
    problem(`${where}: ${JSON.stringify(got)?.slice(0, 120)} != ${JSON.stringify(want)?.slice(0, 120)}`);
  }
}

// The site holds what the page needs, and says it is the web studio.
const page = readFileSync(join(site, 'index.html'), 'utf8');
if (!page.includes('<meta name="statclaim-backend" content="browser">')) problem('index.html does not select the browser backend');
for (const name of ['worker.js', 'python.js', 'backend.js', 'python/manifest.json', 'python/api.py', 'pyodide/NOTICE.txt']) {
  if (!existsSync(join(site, name))) problem(`the site has no ${name}`);
}

const started = Date.now();
const { loadPyodide } = await import(pathToFileURL(join(site, 'pyodide/pyodide.mjs')).href);
const answer = await startStatClaim(loadPyodide, {
  indexURL: join(site, 'pyodide') + '/',
  read: async path => new Uint8Array(readFileSync(join(site, path))),
});
console.log(`StatClaim started in Pyodide in ${((Date.now() - started) / 1000).toFixed(1)} s`);

// The written answers are what Pyodide gives too, for the endpoints that read no files.
const capabilities = JSON.parse(readFileSync(join(site, 'api/capabilities.json'), 'utf8'));
for (const name of ['blocks', 'capabilities']) {
  compare(JSON.parse(answer('GET', name).body), JSON.parse(readFileSync(join(site, `api/${name}.json`), 'utf8')), `GET ${name}`);
}
if (capabilities.where !== 'browser' || capabilities.lean !== false) problem('the web studio must say it has no Lean');
if (!capabilities.links?.codespaces) problem('the web studio has no link to the full studio');

// Every example and lesson compiles and runs as on CPython, and no proof is attempted.
const reference = JSON.parse(readFileSync(referenceFile, 'utf8'));
let runs = 0;
for (const [path, expected] of Object.entries(reference)) {
  for (const name of ['compile', 'run']) {
    const got = answer('POST', name, JSON.stringify({source: expected.source, name: expected.name}));
    const [status, body] = expected[name];
    if (got.status !== status) { problem(`${path} ${name}: status ${got.status}, expected ${status}`); continue; }
    const result = JSON.parse(got.body);
    compare(result, body, `${path} ${name}`);
    if (name !== 'run') continue;
    runs++;
    for (const request of result.requests || []) {
      const proof = capabilities.lean_operations.includes(request.operation);
      if (proof && !['needs_lean', 'unresolved_obligation'].includes(request.status)) problem(`${path}: ${request.name} ran a proof (${request.status})`);
      if (request.status === 'backend_error') problem(`${path}: ${request.name} reached the backend`);
    }
  }
}
console.log(`Compared ${runs} studies with CPython in ${((Date.now() - started) / 1000).toFixed(1)} s`);
for (const text of problems) console.log(text);
process.exit(problems.length ? 1 : 0);
