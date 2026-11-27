import { mountDocument, applyEdits } from './document.js';
import { request as backendRequest, prepare, onState, where } from './backend.js';
import { mountPalette, miniBlock } from './palette.js';
import { openWizard, DESIGNS, FAMILIES as DESIGN_FAMILIES } from './wizard.js';
import { el, button, icon, human, title, familyOf, FAMILIES, SHAPES, keyGlyph, derivationView, codeTitle, statusText, plural, messageBlock, outcome, outcomeBadge, headline, valueText, setFamily, calculationLines, powerCurve, certStamp, scrollInside, fixBox } from './ui.js';

const byId = id => document.getElementById(id);
const app = byId('app');
const picker = byId('lesson');
const host = byId('lessonBlocks');
const sourceBox = byId('source');
const report = byId('report');
const documents = new Map();
let catalog;
let palette;
// What this studio can do. Without Lean, checks that build proofs say so and point the way.
let capabilities = {where: 'server', lean: true, lean_operations: [], links: {}};
const leanHelpKey = 'statclaim.studio.leanHelpSeen';
let canvas;
let active;
let generation = 0;
let timer;
let request;
let previewTimer;
let previewRequest;
let previewId = 0;
let sequence = 0;
let helpSig = null;
let lastShown = null;
const callFamily = new Map();
const signatures = new Map();
// Drafts outlive the tab, so closing it never loses edits. Version 1 kept them per tab.
const draftKey = 'statclaim.studio.drafts.v2';
const oldDraftKey = 'statclaim.studio.drafts.v1';
const visitKey = 'statclaim.studio.visit';
const layoutKey = 'statclaim.studio.layout.v1';
const wiresKey = 'statclaim.studio.wires.v1';
let showWires = false;
try { showWires = window.localStorage.getItem(wiresKey) === 'on'; } catch { /* optional */ }
let layouts = {};
try { layouts = JSON.parse(window.localStorage.getItem(layoutKey) || '{}') || {}; } catch { /* optional */ }
// Stack positions are a per-browser convenience, kept beside the drafts rather than in the .stat file.
function saveLayout(key, map) {
  if (map) layouts[key] = map; else delete layouts[key];
  try { window.localStorage.setItem(layoutKey, JSON.stringify(layouts)); } catch { /* optional */ }
}
const panelKey = 'statclaim.studio.panel.v1';

// The app fills the window; the page itself never scrolls.
if ('scrollRestoration' in window.history) window.history.scrollRestoration = 'manual';
document.scrollingElement?.scrollTo?.(0, 0);
byId('undo').append(icon('undo'));
byId('redo').append(icon('redo'));
byId('historyButton').append(icon('history'));
byId('togglePanel').append(icon('panel'));
byId('runChecks').prepend(icon('play'));
// New study is the way in for most people, so it wears the block colours and nudges once.
{
  const newButton = byId('newDoc');
  const mark = el('span', 'new-study-mark');
  mark.setAttribute('aria-hidden', 'true');
  for (const family of ['study', 'null', 'analysis']) { const piece = el('span'); piece.dataset.family = family; mark.append(piece); }
  newButton.prepend(mark);
  try { if (!window.localStorage.getItem('statclaim.studio.wizardSeen')) newButton.classList.add('beckon'); } catch { /* optional */ }
}
byId('openFile').parentElement.prepend(icon('open'));
for (const [id, name] of [['showLinks', 'link'], ['showReadings', 'note'], ['arrangeFlow', 'flow'], ['zoomFit', 'fit'], ['cleanUp', 'grid'], ['collapseAll', 'collapse'], ['expandAll', 'expand'], ['zoomOut', 'minus'], ['zoomIn', 'plus']]) byId(id).append(icon(name));

function cancelPreview() {
  clearTimeout(previewTimer);
  previewRequest?.abort();
  previewId++;
}
let draftWarned = false;
function saveDrafts() {
  try {
    const drafts = [];
    for (const [key, doc] of documents) {
      if (key.startsWith('local/') || doc.original !== doc.source) {
        drafts.push({key, name: doc.name, source: doc.source, original: doc.original, saved: doc.saved, practice: doc.practice});
      }
    }
    window.localStorage.setItem(draftKey, JSON.stringify({selected: picker.value, drafts}));
  } catch {
    if (!draftWarned) toast('This browser could not keep a draft. Save the study to keep your edits.');
    draftWarned = true;
  }
}
function storedDrafts() {
  try {
    const saved = JSON.parse(window.localStorage.getItem(draftKey) || 'null');
    if (saved) return saved;
    return JSON.parse(window.sessionStorage.getItem(oldDraftKey) || 'null');
  } catch { return null; }
}
// Returns the study to open and how many studies came back with unsaved edits.
function recoverDrafts(group) {
  const saved = storedDrafts();
  let edited = 0;
  for (const d of saved?.drafts || []) {
    if (typeof d.source !== 'string' || typeof d.original !== 'string' || typeof d.name !== 'string') continue;
    const local = /^local\/(\d+)$/.exec(d.key);
    if (local) {
      sequence = Math.max(sequence, Number(local[1]));
      register(d.key, d.name, d.original, group);
    }
    let doc = documents.get(d.key);
    if (doc && doc.original !== d.original) {
      // An updated tutorial and the user's draft must both remain available.
      const recovered = 'local/' + ++sequence;
      register(recovered, 'draft-' + d.name, d.original, group);
      doc = documents.get(recovered);
    }
    if (!doc) continue;
    doc.source = d.source;
    if (typeof d.saved === 'string') doc.saved = d.saved;
    if (d.practice?.steps) doc.practice = d.practice;
    if (d.source !== (doc.saved ?? doc.original)) edited++;
  }
  return {selected: saved?.selected, edited};
}

// Saving. Where the browser allows it, a study is saved back to its own file; otherwise it is downloaded.
const STAT_TYPES = [{description: 'StatClaim study', accept: {'text/plain': ['.stat']}}];
const fileAccess = () => typeof window.showSaveFilePicker === 'function';
const handles = (() => {
  let db = null;
  const open = () => db ||= new Promise((resolve, reject) => {
    const request = window.indexedDB.open('statclaim-studio', 1);
    request.onupgradeneeded = () => request.result.createObjectStore('handles');
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
  const run = async (mode, action) => {
    if (!window.indexedDB) return null;
    const store = (await open()).transaction('handles', mode).objectStore('handles');
    return new Promise((resolve, reject) => {
      const request = action(store);
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  };
  return {
    get: key => run('readonly', store => store.get(key)).catch(() => null),
    set: (key, handle) => run('readwrite', store => store.put(handle, key)).catch(() => null),
  };
})();
async function writable(handle) {
  if (!handle.queryPermission) return true;
  if (await handle.queryPermission({mode: 'readwrite'}) === 'granted') return true;
  return await handle.requestPermission({mode: 'readwrite'}) === 'granted';
}
async function save({as = false} = {}) {
  if (!active) return;
  let doc = active;
  if (!fileAccess()) return download();
  const source = doc.source;
  try {
    let handle = as ? null : doc.handle || await handles.get(doc.key);
    if (handle && !await writable(handle)) handle = null;
    handle ||= await window.showSaveFilePicker({suggestedName: doc.name, types: STAT_TYPES});
    const stream = await handle.createWritable();
    await stream.write(source);
    await stream.close();
    doc = adopt(doc, handle);
    doc.saved = source;
    if (doc === active) controls();
    saveDrafts();
    toast('Saved to ' + handle.name);
  } catch (error) {
    if (error.name === 'AbortError') return;
    toast('Could not save to the file: ' + error.message + ' Downloading a copy instead.');
    download();
  }
}
// A saved file belongs under My studies. A tutorial keeps its original; the edits move to the new file.
function adopt(doc, handle) {
  if (doc.key.startsWith('local/')) {
    doc.handle = handle;
    handles.set(doc.key, handle);
    if (handle.name && handle.name !== doc.name) {
      doc.name = handle.name;
      const option = [...picker.options].find(o => o.value === doc.key);
      if (option) option.textContent = title(doc.name);
      if (doc === active) showName(doc);
    }
    return doc;
  }
  const key = 'local/' + ++sequence;
  register(key, handle.name || doc.name, doc.source, myStudies());
  const copy = documents.get(key);
  Object.assign(copy, {undo: doc.undo, redo: doc.redo, folded: doc.folded, handle, run: doc.run});
  handles.set(key, handle);
  if (layouts[doc.key]) saveLayout(key, layouts[doc.key]);
  Object.assign(doc, {source: doc.original, undo: [], redo: [], run: null});
  select(key);
  return copy;
}
const myStudies = () => picker.querySelector('optgroup[label="My studies"]');
async function openWithPicker() {
  try {
    const [handle] = await window.showOpenFilePicker({types: STAT_TYPES});
    const file = await handle.getFile();
    const source = await file.text();
    const key = addLocal(file.name, source);
    const doc = documents.get(key);
    Object.assign(doc, {handle, saved: source});
    handles.set(key, handle);
    controls();
    toast('Opened ' + file.name);
  } catch (error) {
    if (error.name !== 'AbortError') toast('Could not open the file. ' + error.message);
  }
}
// New study: pick a design, answer a few questions, and get a study that compiles; Start empty
// gives a blank file. start opens it on one design ({design}) or one family's cards ({family}).
function newStudy(start = {}) {
  byId('newDoc').classList.remove('beckon');
  try { window.localStorage.setItem('statclaim.studio.wizardSeen', '1'); } catch { /* optional */ }
  openWizard({
    start,
    check: async source => {
      const result = await api('compile', {source, name: 'new-study.stat'});
      return {errors: (result.diagnostics || []).filter(d => d.severity === 'error').map(d => d.message)};
    },
    onCreate: (name, source) => { addLocal(uniqueName(name), source); toast('Created ' + active.name + '. Every block can be changed.'); },
    onEmpty: () => addLocal('study-' + (sequence + 1) + '.stat', ''),
  });
}
function uniqueName(name) {
  const taken = new Set([...documents.values()].map(doc => doc.name));
  let candidate = name;
  for (let i = 2; taken.has(candidate); i++) candidate = name.replace(/(\.stat)?$/, '-' + i + '.stat');
  return candidate;
}
function addLocal(name, source, {practice, layout} = {}) {
  const key = 'local/' + ++sequence;
  register(key, name, source, myStudies());
  if (practice) documents.get(key).practice = practice;
  if (layout) saveLayout(key, layout);
  select(key);
  return key;
}

async function api(path, body, signal) {
  const options = body ? {
    method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body), signal,
  } : {signal};
  let response;
  try { response = await backendRequest(path, options); }
  catch (error) {
    if (error.name === 'AbortError') throw error;
    throw Object.assign(Error(where === 'browser' ? 'StatClaim stopped responding in this browser. Reload the page.' :
      'The StatClaim checker is not responding. Start the studio server with .venv/bin/python studio/server.py, then press Recheck.'), {offline: true});
  }
  if (response.status === 503) throw Object.assign(Error((await response.json()).error), {offline: true});
  if (!response.ok) throw Error(response.status === 413 ? 'This document exceeds the editor size limit.' :
    response.status === 404 ? (where === 'browser' ? 'This web studio cannot do that yet. Reload the page in case it was updated.' :
      'The running server is older than the editor and cannot do this. Restart it with .venv/bin/python studio/server.py, then reload the page.') :
    'The StatClaim checker could not handle this request (' + response.status + ').');
  const result = await response.json();
  return path === 'compile' ? describeGaps(result) : result;
}
// An empty input is an undeclared choose_ name. Say so in the editor's terms.
const gapMessage = label => 'The ' + label.replace(/^choose_/, '').replace(/_+$/, '').replaceAll('_', ' ') + ' input is empty. Drag a block into it, or click it to choose one.';
function describeGaps(result) {
  for (const d of result.diagnostics || []) {
    const name = d.code === 'unknown_name' && d.message.match(/'(choose_\w*)'/)?.[1];
    if (name) Object.assign(d, {code: 'empty_input', message: gapMessage(name)});
  }
  return result;
}
function walk(node, visit) {
  visit(node);
  for (const child of node.children || []) walk(child, visit);
}
// The compiler stops a statement at its first error and reports every statement that uses it.
// Mark each empty input, and file follow-on errors under the error that causes them.
function organise(result, parsed, source) {
  const statements = parsed?.statements || [];
  const chars = Array.from(source);
  const starts = [0];
  chars.forEach((c, i) => { if (c === '\n') starts.push(i + 1); });
  const offsetOf = span => (starts[span.line - 1] ?? chars.length) + span.column - 1;
  const spanOf = (start, end) => {
    const at = offset => {
      let line = starts.length - 1;
      while (line > 0 && starts[line] > offset) line--;
      return [line + 1, offset - starts[line] + 1];
    };
    const [line, column] = at(start);
    const [endLine, endColumn] = at(end);
    return {path: '<input>', line, column, end_line: endLine, end_column: endColumn};
  };
  const declared = new Set(statements.map(st => st.name).filter(Boolean));
  const diagnostics = result.diagnostics.map(d => ({...d}));
  const seen = new Set(diagnostics.map(d => offsetOf(d.source)));
  const uses = new Map();
  for (const st of statements) {
    const names = new Set();
    walk(st.expression, node => {
      if (node.kind !== 'Reference') return;
      names.add(node.label);
      if (node.label.startsWith('choose_') && !declared.has(node.label) && !seen.has(node.start)) {
        seen.add(node.start);
        diagnostics.push({code: 'empty_input', severity: 'error', message: gapMessage(node.label), source: spanOf(node.start, node.end), synthetic: true});
      }
    });
    if (st.name) uses.set(st.name, names);
  }
  const owner = d => statements.find(st => st.start <= offsetOf(d.source) && offsetOf(d.source) < st.end);
  const reaches = (from, to) => {
    const queue = [from];
    const visited = new Set();
    while (queue.length) {
      const name = queue.shift();
      if (name === to) return true;
      if (visited.has(name)) continue;
      visited.add(name);
      queue.push(...(uses.get(name) || []));
    }
    return false;
  };
  const roots = diagnostics.filter(d => d.code !== 'dependency' && d.severity === 'error');
  // "'design' depends on an invalid declaration" marks a use of design inside another statement.
  for (const d of diagnostics) {
    if (d.code !== 'dependency') continue;
    const used = d.message.match(/'([^']+)' depends on/)?.[1];
    const cause = used && roots.find(r => { const at = owner(r)?.name; return at && reaches(used, at); });
    if (!cause) continue;
    d.cause = owner(cause).name;
    const affected = owner(d)?.name || 'a check';
    cause.affects ||= [];
    if (!cause.affects.includes(affected)) cause.affects.push(affected);
  }
  diagnostics.sort((a, b) => offsetOf(a.source) - offsetOf(b.source));
  return {...result, diagnostics};
}
// What needs fixing first: errors without a cause elsewhere, then open obligations.
const shownOf = result => result.diagnostics.filter(d => !d.cause);
function tally(result) {
  const shown = shownOf(result);
  const errors = shown.filter(d => d.severity === 'error');
  const gaps = errors.filter(d => d.code === 'empty_input').length;
  return {shown, gaps, errors: errors.length - gaps, open: shown.length - errors.length, waiting: result.diagnostics.length - shown.length};
}
const errorWords = ({gaps, errors}) => [gaps && plural(gaps, 'empty input'), errors && plural(errors, 'error')].filter(Boolean).join(' and ');

// Documents -------------------------------------------------------------------
function group(label) {
  const node = document.createElement('optgroup');
  node.label = label;
  picker.append(node);
  return node;
}
// Shipped studies have links, which the address bar shows while one is open:
// ?open=tutorial/01_first_claim, example/fisher, paper/simon_design, or copd/power for a study
// in replication/copd/. The study's path in the repository works too, such as examples/paper/simon_design.
const studyLinks = new Map();
const linkOf = new Map();
function linkStudy(key, link, path) {
  linkOf.set(key, link);
  studyLinks.set(link, key);
  studyLinks.set(path, key);
}
function requestedLink() {
  try {
    const link = new URL(window.location.href).searchParams.get('open');
    return link && link.trim().replace(/^\/+|\/+$/g, '').replace(/\.stat$/i, '');
  } catch { return null; }
}
function showLink(key) {
  try {
    const url = new URL(window.location.href);
    const params = new URLSearchParams(url.search);
    params.delete('open');
    const link = linkOf.get(key);
    url.search = [params.toString(), link && 'open=' + link].filter(Boolean).join('&');
    if (url.href !== window.location.href) window.history.replaceState(window.history.state, '', url.href);
  } catch { /* the address is a convenience */ }
}
async function copyLink() {
  const link = active && linkOf.get(active.key);
  if (!link || !capabilities.links?.studio) return;
  const url = capabilities.links.studio + '?open=' + link;
  try {
    await window.navigator.clipboard.writeText(url);
    toast('Copied the link to ' + title(active.name) + ': ' + url);
  } catch { toast('The link to ' + title(active.name) + ' is ' + url); }
}
function register(key, name, source, parent) {
  documents.set(key, {key, name, source, original: source, undo: [], redo: [], folded: new Set(), issues: 0, scroll: 0});
  const option = document.createElement('option');
  option.textContent = title(name);
  option.value = key;
  parent.append(option);
}
function controls() {
  byId('undo').disabled = !active.undo.length;
  byId('historyButton').disabled = !active.undo.length;
  byId('undo').title = active.undo.length ? 'Undo ' + (active.undo.at(-1).label || 'the last edit') + ' (⌘Z)' : 'Undo (⌘Z)';
  byId('redo').disabled = !active.redo.length;
  byId('restoreLesson').disabled = active.source === active.original;
  // A study saved to a file compares with that file; a tutorial compares with its original.
  const dirty = byId('dirty');
  const filed = typeof active.saved === 'string';
  dirty.hidden = active.source === (filed ? active.saved : active.original);
  dirty.textContent = filed ? 'unsaved' : 'edited';
  dirty.title = filed ? 'Changes not yet saved to ' + active.name : 'Changed from the original';
  byId('download').title = (active.handle ? 'Save to ' + active.name : fileAccess() ? 'Save to a file' : 'Download the .stat file') + ' (⌘S)';
}
function showName(doc) {
  const named = doc.practice ? doc.practice.lessonName : doc.name;
  let label = title(named).replace(/^\d+\s+/, '');
  label = label.charAt(0).toUpperCase() + label.slice(1);
  byId('lessonTitle').textContent = doc.practice ? 'Practice: ' + label : label;
  byId('filename').textContent = doc.name;
  document.title = byId('lessonTitle').textContent + ' · StatClaim Studio';
}
function changedRange(before, after) {
  const a = Array.from(before);
  const b = Array.from(after);
  let start = 0;
  while (start < a.length && start < b.length && a[start] === b[start]) start++;
  let endA = a.length;
  let endB = b.length;
  while (endA > start && endB > start && a[endA - 1] === b[endB - 1]) { endA--; endB--; }
  return {start, end: endB, oldEnd: endA};
}
// Undo steps are named after what changed, such as "Line 7: choose_model → study".
function describeChange(before, after) {
  const range = changedRange(before, after);
  const a = Array.from(before);
  const b = Array.from(after);
  const short = chars => {
    const text = chars.join('').replace(/\s+/g, ' ').trim();
    return text.length > 36 ? text.slice(0, 35) + '…' : text;
  };
  const removed = short(a.slice(range.start, range.oldEnd));
  const added = short(b.slice(range.start, range.end));
  const line = b.slice(0, range.start).filter(c => c === '\n').length + 1;
  if (!removed && !added) return 'Line ' + line + ': spacing';
  return 'Line ' + line + ': ' + (!removed ? 'added ' + added : !added ? 'removed ' + removed : removed + ' → ' + added);
}
// Undo steps hold the source and the stack layout, so moving a stack can be undone too.
const snapshot = doc => layouts[doc.key] ? JSON.parse(JSON.stringify(layouts[doc.key])) : null;
function layoutChanged(doc, map, extra = {}) {
  if (extra.commit) {
    // A burst of keyboard nudges is one undo step.
    if (!(extra.coalesce && Date.now() - (doc.lastNudge || 0) < 900)) {
      doc.undo.push({source: doc.source, layout: snapshot(doc), label: extra.label || 'Moved blocks'});
      if (doc.undo.length > 100) doc.undo.shift();
    }
    doc.lastNudge = extra.coalesce ? Date.now() : 0;
    doc.redo.length = 0;
  } else if (!('layoutBefore' in doc)) doc.layoutBefore = snapshot(doc);
  saveLayout(doc.key, map);
  if (doc === active) controls();
}
function changeSource(next, remember = true, range, meta = {}) {
  if (active.source === next) return;
  active.highlight = range || changedRange(active.source, next);
  active.refocus = Boolean(meta.refocus);
  const layoutBefore = 'layoutBefore' in active ? active.layoutBefore : snapshot(active);
  delete active.layoutBefore;
  if (remember) {
    active.undo.push({source: active.source, layout: layoutBefore, label: describeChange(active.source, next)});
    if (active.undo.length > 100) active.undo.shift();
    active.redo.length = 0;
  } else if (meta.typing && active.undo.length) {
    // A burst of typing is one undo step, named after everything it changed.
    active.undo.at(-1).label = describeChange(active.undo.at(-1).source, next);
  }
  active.edited = true;
  active.source = next;
  if (sourceBox.value !== next) sourceBox.value = next;
  paintCode();
  controls();
  saveDrafts();
  schedule();
}
function history(from, to) {
  if (!active?.[from].length) return;
  const entry = active[from].pop();
  active[to].push({source: active.source, layout: snapshot(active), label: entry.label});
  saveLayout(active.key, entry.layout);
  if (entry.source !== active.source) changeSource(entry.source, false);
  else { controls(); remount(); }
}
// The history list: recent edits by name, newest first; choosing one undoes back to before it.
let historyBox = null;
function closeHistory() {
  historyBox?.remove();
  historyBox = null;
}
function openHistory() {
  if (historyBox) return closeHistory();
  if (!active) return;
  const anchor = byId('historyButton');
  historyBox = el('div', 'history-pop');
  historyBox.setAttribute('role', 'menu');
  historyBox.append(el('strong', 'history-title', 'Recent edits'));
  const entries = active.undo.slice(-15).reverse();
  if (!entries.length) historyBox.append(el('p', 'history-empty', 'Nothing to undo yet.'));
  entries.forEach((entry, i) => {
    const item = button('', () => {
      for (let n = 0; n <= i; n++) history('undo', 'redo');
      closeHistory();
      toast('Undid ' + plural(i + 1, 'edit'));
    }, 'history-item');
    item.setAttribute('role', 'menuitem');
    item.append(el('span', 'history-label', entry.label || 'Edit'), el('span', 'history-hint', i ? 'undo ' + (i + 1) : 'undo'));
    historyBox.append(item);
  });
  if (active.redo.length) historyBox.append(el('p', 'history-empty', plural(active.redo.length, 'edit') + ' can be redone with ⇧⌘Z.'));
  document.body.append(historyBox);
  const box = anchor.getBoundingClientRect();
  historyBox.style.left = Math.max(8, Math.min(box.left, window.innerWidth - 330)) + 'px';
  historyBox.style.top = box.bottom + 6 + 'px';
  historyBox.querySelector('button')?.focus();
  historyBox.addEventListener('keydown', event => { if (event.key === 'Escape') { closeHistory(); anchor.focus(); } });
}
document.addEventListener('pointerdown', event => {
  if (historyBox && !historyBox.contains(event.target) && event.target.closest?.('#historyButton') === null) closeHistory();
}, true);
function select(key) {
  if (active) active.scroll = host.scrollTop;
  active = documents.get(key);
  picker.value = key;
  showName(active);
  byId('notice').textContent = '';
  sourceBox.value = active.source;
  active.highlight = null;
  active.restoreScroll = true;
  closeCompletion();
  hideHover();
  byId('practice').hidden = true;
  const lesson = !key.startsWith('local/');
  byId('practiceStart').hidden = !(lesson || active.practice);
  byId('practiceStart').textContent = active.practice ? 'Practice checklist' : 'Practice this lesson';
  renderResults();
  paintCode();
  controls();
  saveDrafts();
  showLink(key);
  schedule(0);
}

// Status, problems and code -------------------------------------------------------
function stateOf(result) {
  if (result.diagnostics.some(d => d.severity === 'error')) return 'error';
  return result.diagnostics.length ? 'warning' : 'ready';
}
function setStatus(state, text) {
  const status = byId('status');
  status.dataset.state = state;
  byId('statusText').textContent = text;
  status.title = text + ' · show problems';
}
function statusLabel(result) {
  const counts = tally(result);
  if (counts.gaps || counts.errors) return errorWords(counts);
  if (counts.open) return plural(counts.open, 'open obligation');
  return statusText(result.status);
}
function lineStarts(text) {
  const starts = [0];
  for (const line of text.split('\n')) starts.push(starts.at(-1) + line.length + 1);
  return starts;
}
function selectSpan(span) {
  openTab('code', true);
  sourceBox.focus();
  // The textarea counts UTF-16 units, Python counts code points.
  const lines = sourceBox.value.split('\n');
  const index = (line, column) => lines.slice(0, line - 1).reduce((n, s) => n + s.length + 1, 0)
    + Array.from(lines[line - 1] || '').slice(0, column - 1).join('').length;
  sourceBox.setSelectionRange(index(span.line, span.column), index(span.end_line, span.end_column));
  const line = byId('highlight').querySelectorAll('.line')[span.line - 1];
  if (line) sourceBox.scrollTop = Math.max(0, line.offsetTop - sourceBox.clientHeight / 3);
}
const drawer = () => window.matchMedia?.('(max-width: 1180px)').matches;
function reveal(span) {
  if (drawer()) setPanel(false, false);
  const found = canvas?.reveal(span);
  if (!found) selectSpan(span);
}
function renderProblems(result, {preview = false, parseErrors = []} = {}) {
  const state = stateOf(result);
  report.dataset.state = state;
  report.replaceChildren();
  const summary = el('div', 'report-summary');
  const badge = el('span', 'report-icon');
  badge.append(icon(state === 'ready' ? 'check' : state === 'warning' ? 'alert' : 'x'));
  const words = el('div', 'report-words');
  const counts = tally(result);
  const {shown, open} = counts;
  const errors = counts.gaps + counts.errors;
  const headline = preview ? (state === 'ready' ? 'This edit compiles' : state === 'error' ? 'This edit has ' + errorWords(counts) : 'This edit is valid, with ' + plural(open, 'open obligation')) :
    state === 'ready' ? 'StatClaim compiled this study.' : state === 'error' ? errorWords(counts) + ' to fix' : 'Valid, with ' + plural(open, 'open obligation');
  words.append(el('strong', '', headline));
  const detail = preview ? 'Press Enter or leave the field to keep it, or Escape to undo it.' :
    state === 'ready' ? (result.status && result.status !== 'elaborated' ? 'Status: ' + statusText(result.status) : 'Every block fits its inputs and every check is well formed.') :
      state === 'error' ? 'The file is invalid until these are fixed. Press F8 to go to each one in turn.' + (counts.waiting ? ' ' + plural(counts.waiting, 'value waits', 'values wait') + ' on them.' : '') :
        'The file is valid, but a requirement is still open, so the claim is not established. Click one to see its block.';
  words.append(el('span', '', detail));
  summary.append(badge, words);
  report.append(summary);
  const count = byId('problemCount');
  count.hidden = !shown.length;
  count.textContent = String(shown.length);
  count.dataset.state = state;
  if (!shown.length) {
    if (!preview) report.append(el('p', 'report-empty', 'Nothing needs your attention. Add a check such as verify(typeI(analysis)) to ask for a guarantee.'));
    return;
  }
  const list = el('ol', 'problems');
  for (const diagnostic of shown) {
    const item = el('li', 'problem');
    item.dataset.severity = diagnostic.severity === 'error' ? 'error' : 'warning';
    const mark = el('span', 'problem-icon');
    mark.append(icon(diagnostic.severity === 'error' ? 'alert' : 'info'));
    const main = el('div', 'problem-main');
    const head = el('div', 'problem-title');
    head.append(el('strong', '', codeTitle(diagnostic.code)), el('span', 'problem-kind', diagnostic.severity === 'error' ? 'error' : 'open obligation'), el('code', 'problem-code', diagnostic.code));
    const go = button('', () => reveal(diagnostic.source), 'problem-go');
    go.append(icon('target'), el('span', '', 'Line ' + diagnostic.source.line + ' · show block'));
    main.append(head, messageBlock(diagnostic.message, 'problem-msg'));
    const found = !preview && canvas?.fixes?.(diagnostic.source);
    if (found) main.append(fixBox(found));
    item.addEventListener('mouseenter', () => canvas?.peek(diagnostic.source, true));
    item.addEventListener('mouseleave', () => canvas?.peek(diagnostic.source, false));
    const actions = el('div', 'problem-actions');
    actions.append(go, button('Show in code', () => selectSpan(diagnostic.source), 'problem-link'));
    main.append(actions);
    // Values that fail only because they use this one.
    if (diagnostic.affects?.length) {
      const waiting = el('div', 'problem-waiting');
      waiting.append(el('span', '', 'Also waiting on this:'));
      for (const name of diagnostic.affects) {
        const jump = button(name, () => canvas?.focusName?.(name), 'problem-chip');
        jump.title = name + ' cannot be checked until this is fixed';
        waiting.append(jump);
      }
      main.append(waiting);
    }
    if (diagnostic.related?.length) {
      const related = el('ul', 'problem-related');
      for (const entry of diagnostic.related) {
        const row = el('li');
        const jump = button('', () => reveal(entry.source), 'problem-link');
        jump.append(el('span', '', 'Line ' + entry.source.line + ' · ' + entry.message));
        row.append(jump);
        related.append(row);
      }
      main.append(related);
    }
    item.append(mark, main);
    list.append(item);
  }
  report.append(list);
  if (parseErrors.length && !preview) report.prepend(el('p', 'report-note', 'Some lines could not be read, so their blocks are missing from the canvas.'));
}
function showResult(result, parsed) {
  setStatus(stateOf(result), statusLabel(result));
  renderProblems(result, {parseErrors: parsed?.parse_errors || []});
  paintCode(result.diagnostics);
  lastShown = result;
}

const escape = text => text.replace(/[&<>]/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;'}[c]));
const TOKEN = /(#[^\n]*)|("(?:\\.|[^"\\\n])*"?)|(\b\d+(?:\.\d+)?(?:\s*\/\s*\d+)?\b)|\b(use|let)\b|([A-Za-z_][\w]*)(?=\s*\()|([A-Za-z_]\w*)(?=\s*=(?!=))|([A-Za-z_][\w.]*)/g;
// Lines added, changed or removed since the original lesson or the saved file, by a line diff.
function lineDiff(before, after) {
  const a = before.split('\n');
  const b = after.split('\n');
  const rows = a.length + 1;
  const cols = b.length + 1;
  if (rows * cols > 4e6) return null;
  const table = new Uint32Array(rows * cols);
  for (let i = a.length - 1; i >= 0; i--) {
    for (let j = b.length - 1; j >= 0; j--) {
      table[i * cols + j] = a[i] === b[j] ? table[(i + 1) * cols + j + 1] + 1 : Math.max(table[(i + 1) * cols + j], table[i * cols + j + 1]);
    }
  }
  const marks = new Map();
  let i = 0;
  let j = 0;
  let removed = 0;
  const flush = line => { if (removed) { marks.set(line, marks.get(line) === 'added' ? 'changed' : marks.get(line) || 'removed'); removed = 0; } };
  while (i < a.length || j < b.length) {
    if (i < a.length && j < b.length && a[i] === b[j]) { flush(j); i++; j++; }
    else if (j < b.length && (i === a.length || table[i * cols + j + 1] > table[(i + 1) * cols + j])) {
      marks.set(j, removed ? 'changed' : 'added');
      if (removed) removed--;
      j++;
    } else { removed++; i++; }
  }
  flush(Math.max(0, b.length - 1));
  return marks;
}
function paintCode(diagnostics = lastShown?.diagnostics || []) {
  const text = sourceBox.value;
  const lines = text.split('\n');
  const baseline = active ? active.saved ?? active.original : text;
  const changes = baseline === text ? new Map() : lineDiff(baseline, text) || new Map();
  const changeNote = byId('changeNote');
  if (changeNote) {
    const count = changes.size;
    changeNote.textContent = count ? ' · ' + plural(count, 'line') + ' changed from ' + (typeof active?.saved === 'string' ? 'the saved file' : 'the original') : '';
  }
  const marks = new Map();
  for (const d of diagnostics) {
    if (d.cause) continue;
    for (let line = d.source.line; line <= d.source.end_line; line++) {
      if (marks.get(line) !== 'error') marks.set(line, d.severity === 'error' ? 'error' : 'warning');
    }
  }
  byId('highlight').innerHTML = lines.map((line, i) => {
    const body = escape(line).replace(TOKEN, (match, comment, string, num, keyword, call, arg, name) => {
      if (comment) return '<span class="t-comment">' + comment + '</span>';
      if (string) return '<span class="t-string">' + string + '</span>';
      if (num) return '<span class="t-number">' + num + '</span>';
      if (keyword) return '<span class="t-keyword">' + keyword + '</span>';
      if (call) return '<span class="t-call" data-family="' + (callFamily.get(call) || 'other') + '">' + call + '</span>';
      if (arg) return '<span class="t-arg">' + arg + '</span>';
      return '<span class="t-name">' + name + '</span>';
    });
    const mark = marks.get(i + 1);
    return '<span class="line' + (mark ? ' line-' + mark : '') + '">' + (body || ' ') + '</span>';
  }).join('');
  const gutter = byId('gutter');
  gutter.replaceChildren(...lines.map((_, i) => {
    const number = el('span', 'ln' + (marks.has(i + 1) ? ' ln-' + marks.get(i + 1) : '') + (changes.has(i) ? ' diff-' + changes.get(i) : ''), String(i + 1));
    if (changes.has(i)) number.title = {added: 'Added', changed: 'Changed', removed: 'Lines removed above'}[changes.get(i)] + ' since ' + (typeof active?.saved === 'string' ? 'the last save' : 'the original');
    return number;
  }));
  syncScroll();
}
function syncScroll() {
  const highlight = byId('highlight');
  highlight.scrollTop = sourceBox.scrollTop;
  highlight.scrollLeft = sourceBox.scrollLeft;
  byId('gutter').scrollTop = sourceBox.scrollTop;
}

// Side panel ----------------------------------------------------------------------
const TABS = ['problems', 'results', 'code', 'help'];
function openTab(name, reveal = false) {
  for (const tab of TABS) {
    const selected = tab === name;
    byId('tab-' + tab).setAttribute('aria-selected', String(selected));
    byId('tab-' + tab).tabIndex = selected ? 0 : -1;
    byId('panel-' + tab).hidden = !selected;
  }
  if (name === 'help') renderHelp(helpSig);
  if (name === 'results') renderResults();
  if (name === 'code') window.requestAnimationFrame?.(syncScroll);
  if (reveal) setPanel(true);
}
function currentTab() { return TABS.find(tab => byId('tab-' + tab).getAttribute('aria-selected') === 'true'); }
function setPanel(open, remember = !drawer()) {
  app.classList.toggle('panel-closed', !open);
  byId('togglePanel').setAttribute('aria-expanded', String(open));
  if (remember) try { window.localStorage.setItem(panelKey, open ? 'open' : 'closed'); } catch { /* optional */ }
}
function showHelp(sig, soft) {
  helpSig = sig;
  if (soft && currentTab() !== 'help') return;
  if (soft && app.classList.contains('panel-closed')) return;
  openTab('help', !soft);
}
function chip(type) {
  const node = el('span', 'type-chip', type);
  node.dataset.family = familyOf(type);
  return node;
}
function renderHelp(sig) {
  const box = byId('help');
  box.replaceChildren();
  if (!sig) {
    box.append(el('h2', 'help-title', 'How the studio works'));
    const steps = el('ol', 'help-steps');
    for (const [head, text] of [
      ['Drag or click a block', 'Pick a block in the palette, then click a glowing input or the canvas. You can also drag it.'],
      ['Colours show what fits', 'An input only accepts blocks of its own colour. Empty inputs show the type they need.'],
      ['Click to change', 'Click a value to replace it, a number to type, or a block name for more options.'],
      ['StatClaim checks every edit', 'Problems appear as red badges on their block and in the Problems tab.'],
    ]) {
      const item = el('li');
      item.append(el('strong', '', head), el('span', '', text));
      steps.append(item);
    }
    box.append(steps, el('h3', 'help-sub', 'Colours'));
    const legend = el('ul', 'help-legend');
    for (const [family, label] of Object.entries(FAMILIES)) {
      if (family === 'other') continue;
      const row = el('li');
      const sample = el('span', 'legend-swatch');
      sample.dataset.family = family;
      row.append(sample, label);
      legend.append(row);
    }
    box.append(legend, el('h3', 'help-sub', 'Shortcuts'));
    const keys = el('dl', 'help-keys');
    for (const [key, text] of [['⌘ Z', 'Undo'], ['⇧ ⌘ Z', 'Redo'], ['⌘ S', 'Save .stat'], ['/', 'Search blocks'], ['Esc', 'Cancel placing or close a menu']]) {
      const row = el('div');
      row.append(el('dt', '', key), el('dd', '', text));
      keys.append(row);
    }
    box.append(keys, el('p', 'help-tip', 'Hover over a block in the palette to read about it here.'));
    return;
  }
  const head = el('div', 'help-head');
  const sample = miniBlock(sig, 'pal-block help-block');
  sample.tabIndex = -1;
  sample.setAttribute('aria-hidden', 'true');
  head.append(sample);
  const place = button('', () => canvas?.arm(sig), 'btn small primary');
  place.append(icon('plus'), 'Place in study');
  head.append(place);
  box.append(head);
  const makes = el('p', 'help-makes');
  makes.append('Makes ', chip(sig.result || 'value'));
  if (sig.tier) {
    const tier = el('span', 'tier tier-' + sig.tier, sig.tier);
    makes.append(' ', tier);
  }
  box.append(makes);
  const params = Object.entries(sig.parameters || {});
  if (params.length) {
    box.append(el('h3', 'help-sub', 'Inputs'));
    const list = el('dl', 'help-params');
    for (const [name, type] of params) {
      const row = el('div');
      const term = el('dt', '', human(name));
      if ((sig.optional || []).includes(name)) term.append(el('span', 'optional', 'optional'));
      const def = el('dd');
      def.append(chip(type));
      const choices = sig.choices?.[name] || Object.keys(catalog.enumerations?.[sig.name + ' ' + name] || {});
      if (choices.length) def.append(el('small', '', choices.map(human).join(' · ')));
      row.append(term, def);
      list.append(row);
    }
    box.append(list);
  }
  if (sig.description) box.append(el('h3', 'help-sub', 'What it does'), el('p', 'help-text', sig.description));
  if (sig.contract?.expected_null) box.append(el('h3', 'help-sub', 'Null it supports'), el('p', 'help-text', sig.contract.expected_null));
  if (sig.module) {
    const info = catalog.module_info?.[sig.module];
    box.append(el('h3', 'help-sub', 'Module'));
    const line = el('p', 'help-text');
    line.append(el('code', '', 'use ' + sig.module));
    if (info?.classification) line.append(' · ' + info.classification);
    box.append(line);
    if (info?.support) box.append(el('p', 'help-text muted', info.support));
  }
  if (sig.typed_signature) box.append(el('h3', 'help-sub', 'Signature'), el('pre', 'help-sig', sig.typed_signature));
  box.append(button('Back to the guide', () => { helpSig = null; renderHelp(null); }, 'btn ghost small'));
}

// Toasts and banners ---------------------------------------------------------------
function toast(message, {undo} = {}) {
  const node = el('div', 'toast');
  node.setAttribute('role', 'status');
  node.append(el('span', '', message));
  const dismiss = () => { node.classList.add('leaving'); setTimeout(() => node.remove(), 250); };
  if (undo) node.append(button('Undo', () => { history('undo', 'redo'); dismiss(); }, 'toast-action'));
  byId('toasts').append(node);
  byId('notice').textContent = message;
  setTimeout(dismiss, undo ? 6000 : 3600);
}
function setBanner(message, action, glyph = 'alert') {
  const banner = byId('banner');
  banner.replaceChildren();
  banner.hidden = !message;
  if (!message) return;
  // A notice, such as StatClaim starting in the browser, is not an error.
  banner.dataset.tone = glyph === 'info' ? 'info' : 'alert';
  banner.setAttribute('role', glyph === 'info' ? 'status' : 'alert');
  banner.append(icon(glyph), el('span', '', message));
  if (action) banner.append(button(action[0], action[1], 'btn small'));
}

// Checking ---------------------------------------------------------------------------
function preview(source, version) {
  if (generation !== version) return Promise.resolve(null);
  cancelPreview();
  const id = previewId;
  setStatus('pending', 'Checking edit…');
  return new Promise(resolve => {
    previewTimer = setTimeout(async () => {
      previewRequest = new AbortController();
      try {
        const result = await api('compile', {source, name: active.name}, previewRequest.signal);
        if (previewId !== id || generation !== version) return resolve(null);
        setStatus(stateOf(result), 'Preview · ' + statusLabel(result));
        renderProblems(result, {preview: true});
        resolve(result);
      } catch (error) {
        if (previewId === id && version === generation && error.name !== 'AbortError') {
          setStatus('offline', 'Checker offline');
          report.textContent = error.message;
        }
        resolve(null);
      }
    }, 220);
  });
}
function legend() {
  const families = new Set([...host.querySelectorAll('.stack[data-family], .blk[data-family]')].map(n => n.dataset.family));
  const box = byId('legend');
  box.replaceChildren();
  for (const [family, label] of Object.entries(FAMILIES)) {
    if (!families.has(family) || ['value', 'other'].includes(family)) continue;
    const item = el('span', 'legend-item');
    // The legend shows each colour with its connector shape.
    let swatch = keyGlyph(family);
    if (swatch) item.title = label + ': ' + SHAPES[family] + ' connector';
    else {
      swatch = el('span', 'legend-swatch');
      swatch.dataset.family = family;
    }
    item.append(swatch, label);
    box.append(item);
  }
}
// Draw the canvas for the document's latest compile, with its run results.
function mount(current, {keepScroll = false} = {}) {
  const {parsed, result, version} = current.view;
  const scroll = current.restoreScroll && !keepScroll ? {top: current.scroll || 0, left: 0} : {top: host.scrollTop, left: host.scrollLeft};
  const errors = result.diagnostics.length;
  const shake = current.edited && errors > current.issues;
  current.issues = errors;
  canvas = mountDocument(host, {
    ...catalog, ...parsed, folded: current.folded, bindings: result.bindings || {},
    diagnostics: result.diagnostics, scroll, highlight: current.highlight, refocus: current.refocus, shake, enter: current.restoreScroll && !keepScroll,
    layout: layouts[current.key] || null, onLayout: (map, extra) => layoutChanged(current, map, extra),
    trash: byId('library'), overlay: byId('overlay'), dock: byId('dock'),
    results: resultsFor(current), canRun: canRun(current), onRun: () => runChecks(), onShowResult: id => showResults(id),
    lean: capabilities.lean, leanOperations: capabilities.lean_operations, onNeedsLean: () => openLeanHelp(),
    wires: showWires,
    onChange: (next, range, meta) => { if (version === generation) changeSource(next, true, range, meta); },
    onScrubbed: () => { if (current.run && !current.run.error) current.recalculate = true; },
    onPreview: next => preview(next, version),
    onCancelPreview: () => {
      if (version !== generation) return;
      cancelPreview();
      showResult(result, parsed);
    },
    onHelp: (sig, soft) => showHelp(sig, soft),
    onArm: sig => { palette?.setArmed(sig); armedSig = sig; hint(); },
    selected: current.selected, onSelect: name => { current.selected = name; hint(); },
    onToast: (message, extra) => toast(message, extra),
    onShowProblems: () => openTab('problems', true),
    onExplain: name => explainFor(current, name),
    onDesign: start => newStudy(start),
  });
  current.highlight = null;
  current.refocus = false;
  current.edited = false;
  current.restoreScroll = false;
  runButton();
  renderResults();
  drawMinimap();
  setTimeout(drawMinimap, 450);
  hint();
}
// The palette hints the blocks that take the selected stack's value, or what an armed
// palette block makes. Python finds them by building each block, so they match the compiler.
let armedSig = null;
let blockFits = null;
function fitsFor(doc, name) {
  if (Object.keys(doc.fits ||= {}).length > 40) doc.fits = {};
  const key = doc.source + '\u0000' + name;
  doc.fits[key] ||= api('fits', {source: doc.source, name: doc.name, declaration: name}).then(result => result.fits);
  return doc.fits[key].catch(error => { delete doc.fits[key]; throw error; });
}
async function hint() {
  const doc = active;
  const sig = armedSig;
  const name = !sig && doc?.view ? doc.selected : null;
  if (!sig && !name) return palette?.hint(null);
  const type = sig ? sig.result : doc.view.result.bindings?.[name]?.type;
  const state = {title: sig ? human(sig.name) : name, family: familyOf(type), block: Boolean(sig), typed: Boolean(type)};
  palette?.hint({...state, pending: true});
  try {
    let fits;
    if (sig) {
      blockFits ||= api('block-fits').catch(error => { blockFits = null; throw error; });
      const table = await blockFits;
      fits = table[sig.module || '']?.[sig.name] || {};
    } else fits = await fitsFor(doc, name);
    if (armedSig !== sig || doc !== active || (name && doc.selected !== name)) return;
    palette?.hint({...state, fits});
    if (name) canvas?.showFits(name, fits);
  } catch {
    if (armedSig === sig && doc === active) palette?.hint(null);
  }
}
// Derivations are cached per source, so asking twice costs nothing.
async function explainFor(doc, name) {
  doc.explained ||= {};
  const key = doc.source + '\u0000' + name;
  doc.explained[key] ||= api('explain', {source: doc.source, name: doc.name, declaration: name}).then(result => result.entries);
  try { return await doc.explained[key]; } catch (error) { delete doc.explained[key]; throw error; }
}
// The minimap shows the whole board in miniature when it does not fit; click or drag it to scroll.
const minimap = byId('minimap');
let minimapFrame = 0;
function drawMinimap() {
  window.cancelAnimationFrame?.(minimapFrame);
  minimapFrame = window.requestAnimationFrame?.(() => {
    // Shown only when some stack lies outside the view.
    const origin = host.getBoundingClientRect();
    const boxes = [...host.querySelectorAll('.stack')].map(card => {
      const box = card.getBoundingClientRect();
      return {card, x: box.left - origin.left + host.scrollLeft, y: box.top - origin.top + host.scrollTop, w: box.width, h: box.height};
    });
    const width = Math.max(host.clientWidth, ...boxes.map(b => b.x + b.w + 20));
    const height = Math.max(host.clientHeight, ...boxes.map(b => b.y + b.h + 20));
    const show = Boolean(active?.view) && boxes.some(b => b.x + b.w > host.scrollLeft + host.clientWidth || b.y + b.h > host.scrollTop + host.clientHeight || b.x < host.scrollLeft || b.y < host.scrollTop);
    minimap.hidden = !show;
    if (!show) return;
    const scale = Math.min(160 / width, 120 / height);
    const svg = minimap.querySelector('svg') || minimap.appendChild(document.createElementNS('http://www.w3.org/2000/svg', 'svg'));
    svg.setAttribute('width', String(Math.round(width * scale)));
    svg.setAttribute('height', String(Math.round(height * scale)));
    svg.setAttribute('viewBox', '0 0 ' + width + ' ' + height);
    svg.replaceChildren();
    const rect = (x, y, w, h, cls) => {
      const node = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
      for (const [k, v] of Object.entries({x, y, width: w, height: h, rx: 6, class: cls})) node.setAttribute(k, String(v));
      svg.append(node);
      return node;
    };
    for (const box of boxes) rect(box.x, box.y, box.w, box.h, 'mini-stack').setAttribute('data-family', box.card.dataset.family || 'other');
    rect(host.scrollLeft, host.scrollTop, host.clientWidth, host.clientHeight, 'mini-view');
    minimap.dataset.scale = String(scale);
  }) || 0;
}
function minimapScroll(event) {
  const scale = Number(minimap.dataset.scale) || 1;
  const box = minimap.querySelector('svg').getBoundingClientRect();
  host.scrollTo?.({left: (event.clientX - box.left) / scale - host.clientWidth / 2, top: (event.clientY - box.top) / scale - host.clientHeight / 2});
}
minimap.addEventListener('pointerdown', event => {
  event.preventDefault();
  minimapScroll(event);
  const move = e => minimapScroll(e);
  const up = () => { document.removeEventListener('pointermove', move); document.removeEventListener('pointerup', up); };
  document.addEventListener('pointermove', move);
  document.addEventListener('pointerup', up);
});
host.addEventListener('scroll', drawMinimap, {passive: true});
window.addEventListener('resize', drawMinimap);
function remount() {
  if (active?.view && active.view.version === generation && !host.inert) mount(active, {keepScroll: true});
}

// Practice ---------------------------------------------------------------------------------
// A lesson becomes an exercise: the links between its values are emptied, and a checklist
// ticks off each one as it is reconnected.
function spanAt(source, start, end) {
  const chars = Array.from(source);
  const at = offset => {
    let line = 1;
    let column = 1;
    for (let i = 0; i < offset && i < chars.length; i++) {
      if (chars[i] === '\n') { line++; column = 1; } else column++;
    }
    return [line, column];
  };
  const [line, column] = at(start);
  const [endLine, endColumn] = at(end);
  return {path: '<input>', line, column, end_line: endLine, end_column: endColumn};
}
function practiceFrom(doc) {
  const statements = doc.view?.parsed.statements || [];
  const declared = new Set(statements.map(st => st.name).filter(Boolean));
  const edits = [];
  const steps = [];
  statements.forEach((st, index) => {
    const visit = (node, path) => (node.children || []).forEach((child, i) => {
      const sig = node.kind === 'Call' ? signatures.get(node.label) : null;
      const param = child.argument || Object.keys(sig?.parameters || {})[i] || (node.kind === 'ListExpr' ? 'item' : 'value');
      if (child.kind === 'Reference' && declared.has(child.label)) {
        edits.push({start: child.start, end: child.end, text: 'choose_' + param});
        steps.push({statement: st.name || null, index, path: [...path, i], param, answer: child.label,
          family: familyOf(doc.view.result.bindings?.[child.label]?.type)});
      } else visit(child, [...path, i]);
    });
    visit(st.expression, []);
  });
  return steps.length ? {source: applyEdits(doc.source, edits), steps} : null;
}
function startPractice() {
  const doc = active;
  if (doc.practice) { byId('practice').hidden = false; doc.practice.hidden = false; renderPractice(); return; }
  const made = practiceFrom(doc);
  if (!made) { toast('This study has no links between values to practise.'); return; }
  const key = addLocal('practice-' + doc.name, made.source, {practice: {lesson: doc.key, lessonName: doc.name, steps: made.steps}, layout: layouts[doc.key]});
  documents.get(key).original = made.source;
  toast('Reconnect ' + plural(made.steps.length, 'link') + '. Press F8 to go to the first one.');
}
function practiceStatus(doc) {
  const statements = doc.view.parsed.statements;
  const chars = Array.from(doc.source);
  return doc.practice.steps.map(step => {
    const st = step.statement ? statements.find(other => other.name === step.statement) : statements[step.index];
    let node = st?.expression;
    for (const i of step.path) node = node?.children?.[i];
    if (!node) return {state: 'missing'};
    if (node.kind === 'Reference' && node.label.startsWith('choose_')) return {state: 'open', node};
    const text = chars.slice(node.start, node.end).join('');
    return {state: text === step.answer ? 'right' : 'different', node, text};
  });
}
function renderPractice() {
  const card = byId('practice');
  const doc = active;
  if (!doc?.practice || !doc.view || doc.practice.hidden) { card.hidden = true; return; }
  card.hidden = false;
  card.replaceChildren();
  const status = practiceStatus(doc);
  const done = status.filter(st => st.state === 'right' || st.state === 'different').length;
  const head = el('header', 'practice-head');
  const titles = el('div', 'practice-titles');
  titles.append(el('strong', '', 'Practice: connect the blocks'), el('span', '', done + ' of ' + status.length + ' links'));
  head.append(titles, button('', () => { doc.practice.hidden = true; saveDrafts(); renderPractice(); }, 'icon-btn practice-close'));
  head.lastChild.append(icon('x'));
  head.lastChild.setAttribute('aria-label', 'Hide the checklist');
  const meter = el('div', 'practice-meter');
  meter.style.setProperty('--done', String(done / status.length));
  card.append(head, meter);
  const counts = tally(doc.view.result);
  if (done === status.length) {
    const ok = !counts.errors && !counts.gaps;
    const differ = status.filter(st => st.state === 'different').length;
    const box = el('div', 'practice-done');
    box.dataset.state = ok ? 'ok' : 'error';
    box.append(el('strong', '', ok ? 'Every link is connected and the study compiles.' : 'Every link is filled, but the study has ' + errorWords(counts) + '.'),
      el('span', '', ok ? (differ ? plural(differ, 'link differs', 'links differ') + ' from the lesson, and the study still compiles.' : 'It matches the lesson exactly.') : 'Press F8 to see what to fix.'));
    const actions = el('div', 'practice-actions');
    if (ok && hasChecks(doc)) actions.append(button('Run checks', () => runChecks(), 'btn small run'));
    if (documents.has(doc.practice.lesson)) actions.append(button('Back to the lesson', () => select(doc.practice.lesson), 'btn small ghost'));
    box.append(actions);
    card.append(box);
  } else if (!done) {
    card.append(el('p', 'practice-intro', 'The links between this lesson\'s values are empty. Drag each value into the input that needs it, or press F8 to go to the next one.'));
  }
  const list = el('ol', 'practice-steps');
  doc.practice.steps.forEach((step, i) => {
    const st = status[i];
    const item = el('li', 'practice-step');
    item.dataset.state = st.state;
    const go = button('', () => {
      if (st.node && st.state === 'open') canvas?.pick(spanAt(doc.source, st.node.start, st.node.end));
      else if (st.node) reveal(spanAt(doc.source, st.node.start, st.node.end));
    }, 'practice-go');
    const mark = el('span', 'practice-mark');
    mark.append(icon(st.state === 'open' || st.state === 'missing' ? 'target' : st.state === 'right' ? 'check' : 'info'));
    go.append(mark, el('span', 'practice-label', human(step.param) + ' of ' + (step.statement || 'the check')));
    item.append(go);
    if (st.state === 'different') item.append(el('span', 'practice-note', 'uses ' + st.text + '; the lesson uses ' + step.answer));
    if (st.state === 'open') {
      const hint = el('details', 'practice-hint');
      hint.append(el('summary', '', 'Hint'));
      const glyph = keyGlyph(step.family);
      const text = el('span', '', 'Takes a ' + (FAMILIES[step.family] || 'value').toLowerCase() + (SHAPES[step.family] ? ', the ' + SHAPES[step.family] + ' connector' : '') + '. ');
      const answer = button('Show answer', () => { answer.replaceWith(el('code', '', step.answer)); }, 'practice-answer');
      hint.append(...[glyph, text, answer].filter(Boolean));
      item.append(hint);
    }
    list.append(item);
  });
  card.append(list);
}
byId('practiceStart').addEventListener('click', startPractice);

// Running checks ------------------------------------------------------------------------
const hasChecks = doc => doc?.view?.parsed.statements.some(function visit(node) {
  const expression = node.expression || node;
  return (expression.kind === 'Call' && Object.hasOwn(catalog.operations, expression.label)) || (expression.children || []).some(visit);
});
const canRun = doc => Boolean(doc?.view) && !doc.view.result.diagnostics.some(d => d.severity === 'error') && hasChecks(doc);
function resultsFor(doc) {
  if (doc.running) return {running: true};
  if (!doc.run) return null;
  return {requests: doc.run.result?.requests || [], values: doc.run.result?.values || {}, outdated: doc.run.outdated || [],
    stale: doc.run.source !== doc.source, recalculating: Boolean(doc.recalculating), error: doc.run.error};
}
// While the study has errors, the run button leads to them one at a time.
const blockers = doc => doc?.view ? tally(doc.view.result) : null;
function runButton() {
  const go = byId('runChecks');
  const counts = blockers(active);
  const guide = Boolean(!active?.running && counts && (counts.gaps || counts.errors));
  go.classList.toggle('running', Boolean(active?.running));
  go.classList.toggle('guide', guide);
  go.disabled = Boolean(active?.running) || !(guide || canRun(active));
  byId('runLabel').textContent = active?.running ? 'Running…' : !guide ? 'Run checks' :
    !counts.errors ? 'Fill ' + plural(counts.gaps, 'input') : !counts.gaps ? 'Fix ' + plural(counts.errors, 'error') : 'Fix ' + plural(counts.gaps + counts.errors, 'problem');
  const glyph = go.querySelector('svg');
  if (glyph?.dataset.kind !== (guide ? 'guide' : 'run')) glyph?.replaceWith(icon(guide ? 'target' : 'play'));
  go.querySelector('svg')?.setAttribute('data-kind', guide ? 'guide' : 'run');
  go.title = active?.running ? 'Running the checks' : guide ? 'Go to the next problem (F8)' : !hasChecks(active) ? 'Add a check such as verify(typeI(analysis)) to run it' :
    'Run every check in this study (⌘↵)' + (capabilities.lean ? '' : '. Proofs need Lean, which this studio cannot run.');
}
// Visits the problems in file order: an empty input opens its chooser, anything else shows its block.
function nextProblem(step = 1) {
  const result = active?.view?.result;
  if (!result) return;
  const shown = shownOf(result);
  const targets = shown.some(d => d.severity === 'error') ? shown.filter(d => d.severity === 'error') : shown;
  if (!targets.length) { toast('Nothing needs fixing'); return; }
  const position = d => d.source.line * 1e6 + d.source.column;
  const here = active.problemAt ?? (step > 0 ? -1 : Infinity);
  const next = step > 0 ? targets.find(d => position(d) > here) || targets[0] :
    [...targets].reverse().find(d => position(d) < here) || targets.at(-1);
  active.problemAt = position(next);
  byId('notice').textContent = codeTitle(next.code) + ', ' + (targets.indexOf(next) + 1) + ' of ' + targets.length + ': ' + next.message;
  if (drawer()) setPanel(false, false);
  if (next.code === 'empty_input' && canvas?.pick(next.source)) return;
  reveal(next.source);
}
async function runChecks() {
  const doc = active;
  if (doc && !doc.running && blockers(doc) && (blockers(doc).gaps || blockers(doc).errors)) return nextProblem();
  if (!doc || doc.running || !canRun(doc)) return;
  const source = doc.source;
  const started = Date.now();
  doc.running = true;
  remount();
  renderResults();
  try {
    const result = await api('run', {source, name: doc.name});
    doc.run = {source, result, seconds: (Date.now() - started) / 1000};
  } catch (error) {
    doc.run = {source, error: error.message, result: {requests: []}};
  }
  doc.running = false;
  if (doc !== active) return;
  remount();
  renderResults();
  openTab('results', true);
  const counts = {};
  for (const request of doc.run.result.requests) {
    const label = outcome(request).label.split(/[,;]/)[0];
    counts[label] = (counts[label] || 0) + 1;
  }
  toast(doc.run.error ? 'The run failed: ' + doc.run.error : Object.entries(counts).map(([label, n]) => n + ' × ' + label.replace(/^./, ch => ch.toLowerCase())).join(' · ') || 'Nothing to run');
  // The first run with a proof it could not build explains why, once per visit.
  const unproved = doc.run.result.requests.filter(request => request.status === 'needs_lean').length;
  if (unproved) {
    let seen = false;
    try { seen = Boolean(window.sessionStorage.getItem(leanHelpKey)); window.sessionStorage.setItem(leanHelpKey, '1'); } catch { /* optional */ }
    if (!seen) openLeanHelp(unproved);
  }
}
// What the run's one Lean build of the whole study shows, as `statclaim report --lean` says it:
// the contract facts Lean decides, what it refutes and what is not in Lean yet. Each claim's
// grade is on its own entry below; a claim is named here only where StatClaim's contract check
// grades it otherwise.
function leanSection(run, stale) {
  const result = run.result?.lean;
  if (!result) return null;
  const section = el('section', 'results-lean');
  section.dataset.state = result.status === 'failed' ? 'failed' : 'checked';
  if (stale || result.outdated) section.classList.add('stale');
  section.append(el('h3', 'results-sub', 'Whole study in Lean'));
  if (result.status === 'failed') {
    // Lean not set up says what to do; any other failure is a disagreement with StatClaim.
    if (result.stage === 'project') {
      section.append(el('p', 'results-lean-summary', result.error));
      return section;
    }
    section.append(el('p', 'results-lean-summary', 'Lean did not check this study, though StatClaim\'s contract check accepts it. This disagreement is a defect; please report it.'));
    const said = disclosure('What Lean said');
    said.append(el('pre', 'results-lean-error', result.error));
    section.append(said);
    return section;
  }
  const claims = result.claims || [];
  const facts = result.contract_facts.length;
  const omitted = result.unproved || [];
  const computed = (run.result.requests || []).some(request => request.status === 'calculated' || request.status === 'simulated');
  section.append(el('p', 'results-lean-summary', 'One Lean build checked the whole study: ' + plural(facts, 'contract fact') +
    (facts === 1 ? ' holds' : ' hold') + (claims.length ? ', and ' + plural(claims.length, 'claim') + (claims.length === 1 ? ' follows from the premises its proof uses.' : ' follow from the premises their proofs use.') : '.') +
    (omitted.length ? ' Lean did not prove ' + plural(omitted.length, 'claim') + ', so ' + (omitted.length === 1 ? 'it stays' : 'they stay') + ' open.' : '') +
    (computed ? ' Calculated and simulated values are not proved in Lean.' : '')));
  for (const claim of claims.filter(claim => claim.python !== claim.grade)) {
    const row = el('p', 'results-note results-lean-python');
    const chip = button(claim.name || claim.claim, () => reveal(claim.source), 'use-chip');
    chip.title = 'Show ' + claim.claim + ' on the canvas, line ' + claim.source.line;
    row.append(chip, ' Lean grades it ' + claim.grade + ', but StatClaim\'s contract check grades it ' + claim.python + '. This disagreement is a defect; please report it.');
    section.append(row);
  }
  for (const [name, reason] of Object.entries(result.refuted || {})) {
    const row = el('p', 'results-note');
    row.append(el('code', '', name), ' ' + (reason === 'no sampling law' ? 'The stopping rule supplies no sampling law for this claim.' : reason));
    section.append(row);
  }
  const left = Object.entries(result.outside_lean || {}).filter(([name]) => !(name in (result.refuted || {})));
  if (left.length) {
    const more = disclosure(plural(left.length, 'part') + ' not in Lean yet');
    const items = el('ul');
    for (const [name, reason] of left) {
      const item = el('li');
      item.append(el('code', '', name), ' ' + reason);
      items.append(item);
    }
    more.append(items);
    section.append(more);
  }
  if (result.certificate_directory) {
    const cert = el('div', 'entry-cert');
    cert.append(el('span', '', 'Certificate'), copyButton(result.certificate_directory));
    cert.title = result.certificate_directory;
    section.append(cert);
  }
  return section;
}
// After a number is dragged, the calculations rerun so values follow the edit. Proofs and cited
// checks keep their last results, marked as from before the edit, until the next full run.
async function recalculate(doc) {
  doc.recalculate = false;
  if (!doc.run || doc.running || doc.recalculating || !canRun(doc)) return;
  const source = doc.source;
  const previous = doc.run;
  doc.recalculating = true;
  if (doc === active) remount();
  let result;
  try { result = await api('run', {source, name: doc.name, only: 'calculate'}); }
  catch { result = null; }
  doc.recalculating = false;
  if (!result || doc.source !== source || doc.run !== previous || doc.running) {
    if (doc === active) remount();
    return;
  }
  doc.run = mergeRun(previous, source, result);
  if (doc !== active) return;
  remount();
  renderResults();
}
function mergeRun(previous, source, fresh) {
  const before = new Map((previous.result?.requests || []).map(request => [request.request_id, request]));
  // Checks line up by number when the edit changed only values, not which checks there are.
  const same = fresh.requests.length === before.size &&
    fresh.requests.every(request => before.get(request.request_id)?.operation === request.operation && before.get(request.request_id)?.claim === request.claim);
  const requests = fresh.requests.map(request => request.status === 'not_executed' && same
    ? {...before.get(request.request_id), outdated: true} : request);
  const kept = requests.some(request => request.outdated);
  const values = {...fresh.values};
  const outdated = [];
  for (const [name, value] of Object.entries(previous.result?.values || {})) {
    if (same && !Object.hasOwn(values, name)) { values[name] = value; outdated.push(name); }
  }
  return {
    source, seconds: previous.seconds, recalculated: true, outdated,
    result: {...fresh, requests, values, status: kept ? previous.result.status : fresh.status,
      run_directory: kept ? previous.result.run_directory : null, certificate_issued: kept && previous.result.certificate_issued,
      lean: kept && previous.result.lean ? {...previous.result.lean, outdated: true} : null},
  };
}
function copyButton(text) {
  const copy = button('Copy path', async () => {
    try { await navigator.clipboard.writeText(text); toast('Copied the path'); }
    catch { toast('Could not copy. The path is ' + text); }
  }, 'btn ghost small');
  return copy;
}
// A row that opens to show more, with the canvas's chevron.
function disclosure(label, cls = '') {
  const box = el('details', ('entry-more ' + cls).trim());
  const summary = el('summary');
  summary.append(icon('chevron'), el('span', '', label));
  box.append(summary);
  return box;
}
function renderResults(focus) {
  const box = byId('results');
  if (!box || !active) return;
  const doc = active;
  box.replaceChildren();
  const badge = byId('resultCount');
  const run = active.run;
  if (active.running) {
    badge.hidden = true;
    const card = el('div', 'results-summary');
    card.dataset.tone = 'running';
    card.append(el('span', 'run-spinner'));
    const words = el('div', 'report-words');
    words.append(el('strong', '', 'Running the checks…'), el('span', '', 'Proofs are built and checked in Lean, which can take 10 to 30 seconds.'));
    card.append(words);
    box.append(card, el('div', 'run-bar wide'));
    return;
  }
  if (!run) {
    badge.hidden = true;
    const empty = el('div', 'results-empty');
    empty.append(el('strong', '', 'Nothing has been run yet.'), el('p', '', 'Run the checks to see what this study establishes and how strong the evidence is.'));
    const go = button('', () => runChecks(), 'btn primary');
    go.append(icon('play'), 'Run checks');
    go.disabled = !canRun(active);
    empty.append(go);
    const legend = el('dl', 'grade-legend');
    for (const [grade, info] of Object.entries(catalog.evidence_grades || {})) {
      const row = el('div');
      const term = el('dt');
      term.append(outcomeBadge({status: {proved: 'verified'}[grade] || grade}));
      row.append(term, el('dd', '', info.meaning));
      legend.append(row);
    }
    empty.append(el('h3', 'help-sub', 'Evidence grades'), legend);
    box.append(empty);
    return;
  }
  const stale = run.source !== active.source;
  const requests = run.result?.requests || [];
  // The head: the file's grade, what it means, and one count per grade.
  const status = run.error ? 'error' : run.result.status;
  const head = el('section', 'results-head');
  const unproved = requests.filter(request => request.status === 'needs_lean').length;
  const meaning = unproved ? plural(unproved, 'check') + (unproved === 1 ? ' needs' : ' need') + ' Lean to build ' + (unproved === 1 ? 'its proof' : 'their proofs') + '; everything else ran.' :
    catalog.program_statuses?.[status] || statusText(status);
  head.append(outcomeBadge({status: run.error ? 'backend_error' : status}, 'outcome big'),
    el('p', 'results-status', run.error || meaning));
  const tones = new Map();
  for (const request of requests) {
    const info = outcome(request);
    tones.set(info.tone, {count: (tones.get(info.tone)?.count || 0) + 1, request});
  }
  if (tones.size > 1) {
    const counts = el('div', 'results-counts');
    for (const [tone, {count, request}] of tones) {
      const chip = outcomeBadge(request, 'outcome count', true);
      chip.dataset.tone = tone;
      chip.lastChild.textContent = count + ' ' + chip.lastChild.textContent.replace(/^./, ch => ch.toLowerCase());
      counts.append(chip);
    }
    head.append(counts);
  }
  const meta = el('p', 'results-meta', plural(requests.length, 'check') + (run.seconds ? ' · ' + run.seconds.toFixed(1) + ' s' : '') + (run.result?.certificate_issued ? ' · certificates written' : ''));
  head.append(meta);
  if (run.result?.run_directory) {
    const where = el('div', 'results-path');
    where.append(el('code', '', run.result.run_directory), copyButton(run.result.run_directory));
    head.append(where);
  }
  box.append(head);
  if (!stale && run.recalculated && requests.some(request => request.outdated)) {
    const note = el('div', 'results-stale');
    note.append(icon('alert'), el('span', '', 'Calculations follow your last edit. The other checks are from before it; run again to bring them up to date.'));
    const again = button('Run again', () => runChecks(), 'btn small');
    again.disabled = !canRun(active);
    note.append(again);
    box.append(note);
  }
  if (stale) {
    const note = el('div', 'results-stale');
    note.append(icon('alert'), el('span', '', 'The study changed after this run. These results describe the earlier version.'));
    const again = button('Run again', () => runChecks(), 'btn small');
    again.disabled = !canRun(active);
    note.append(again);
    box.append(note);
  }
  const lean = leanSection(run, stale);
  if (lean) box.append(lean);
  // Each check looks as it does on the canvas: its block's hat, with what the run found underneath.
  const list = el('ol', 'result-entries');
  let worst = 'proved';
  const rank = ['proved', 'conditional', 'calculated', 'simulated', 'cited', 'declared', 'open', 'error'];
  for (const request of requests) {
    const info = outcome(request);
    if (rank.indexOf(info.tone) > rank.indexOf(worst)) worst = info.tone;
    const entry = el('li', 'result-entry');
    entry.dataset.tone = info.tone;
    entry.dataset.request = request.request_id;
    if (stale || request.outdated) entry.classList.add('stale');
    const hat = button('', () => reveal(request.source), 'entry-hat');
    hat.dataset.family = 'run';
    hat.append(el('span', 'entry-kw', request.name ? 'let' : 'run'));
    if (request.name) hat.append(el('span', 'entry-name', request.name));
    if (request.status === 'verified' && !info.weakest) hat.append(certStamp('cert-medal entry-medal'));
    const op = el('span', 'entry-op', request.operation + ' ' + request.claim + '(' + request.subject + ')');
    op.title = op.textContent;
    hat.append(op, el('span', 'entry-line', 'line ' + request.source.line));
    hat.setAttribute('aria-label', 'Show ' + (request.name || 'this check') + ' on the canvas, line ' + request.source.line);
    hat.title = 'Show this block';
    const panel = el('div', 'entry-panel');
    const top = el('div', 'entry-top');
    top.append(outcomeBadge(request));
    if (info.scope) top.append(el('span', 'entry-scope', info.scope));
    panel.append(top);
    const found = headline(request);
    if (found) {
      const text = el('p', 'entry-headline', found.text);
      if (found.tone) text.dataset.tone = found.tone;
      panel.append(text);
    }
    if (info.weakest) {
      const weak = el('p', 'result-weak');
      weak.append(icon('alert'), el('span', '', 'Only as strong as its weakest part: ' + info.weakest.grade + ' (' + info.weakest.parts.join(', ') + ').'));
      panel.append(weak);
    }
    // A proof that needs Lean says so in its headline, and the button below says what to do.
    if (request.message && !['verified', 'conditional', 'cited', 'declared', 'calculated', 'simulated', 'needs_lean'].includes(request.status)) panel.append(messageBlock(request.message, 'result-message'));
    if (request.status === 'needs_lean') {
      const way = button('', () => openLeanHelp(), 'btn small lean-help-btn');
      way.append(icon('lock'), el('span', '', 'How to get a proof'));
      panel.append(way);
    }
    // The decision is already in the line above the numbers.
    const numeric = ['calculate', 'simulate'].includes(request.operation) || ['calculated', 'simulated'].includes(request.status);
    const lines = (numeric ? calculationLines(request.calculation, request.decision) : [])
      .filter(([term]) => !(found && term === 'Decision'));
    if (request.evidence?.guarantee?.bound) lines.unshift(['Guarantee', human(request.evidence.guarantee.quantity || 'error').replace(/^./, ch => ch.toUpperCase()) + ' ≤ ' + request.evidence.guarantee.bound]);
    if (lines.length) {
      const table = el('dl', 'entry-facts');
      for (const [term, value, title] of lines) {
        const row = el('div');
        const dd = el('dd', '', value);
        if (title) dd.title = title;
        row.append(el('dt', '', term), dd);
        table.append(row);
      }
      panel.append(table);
    }
    const curve = powerCurve(request.calculation);
    if (curve) panel.append(curve);
    if (request.established.length) {
      const established = el('ul', 'entry-established');
      for (const text of request.established) {
        const item = el('li');
        item.append(icon('check'), el('span', '', text));
        established.append(item);
      }
      panel.append(established);
    }
    const assumptions = request.evidence?.assumptions?.length ? request.evidence.assumptions : request.assumptions.map(text => ({text}));
    if (assumptions.length) {
      const more = disclosure(plural(assumptions.length, 'assumption'));
      const items = el('ul');
      for (const item of assumptions) {
        const row = el('li');
        if (item.status) {
          const tag = el('span', 'assumption-tag', item.status);
          tag.dataset.status = item.status;
          tag.title = catalog.assumption_kinds?.[item.kind] || '';
          row.append(tag);
        }
        row.append(el('span', '', item.text));
        items.append(row);
      }
      more.append(items);
      panel.append(more);
    }
    if (request.references.length) {
      const refs = disclosure(plural(request.references.length, 'reference'));
      const items = el('ul');
      for (const text of request.references) items.append(el('li', '', text));
      refs.append(items);
      panel.append(refs);
    }
    // Why the subject fits its contract, fetched when opened.
    if (request.subject) {
      const why = disclosure('Why ' + request.subject + ' fits', 'result-why');
      why.addEventListener('toggle', async () => {
        if (!why.open || why.dataset.loaded) return;
        why.dataset.loaded = 'true';
        const wait = el('p', 'results-note', 'Asking StatClaim…');
        why.append(wait);
        try {
          const entries = await explainFor(doc, request.subject);
          wait.remove();
          if (!entries.length) why.append(el('p', 'results-note', 'There is no contract to explain for ' + request.subject + '.'));
          for (const item of entries) why.append(derivationView(item));
        } catch (error) { wait.textContent = error.message; }
      });
      panel.append(why);
    }
    if (request.certificate) {
      const cert = el('div', 'entry-cert');
      cert.append(el('span', '', 'Certificate'), copyButton(request.certificate));
      cert.title = request.certificate;
      panel.append(cert);
    }
    entry.append(hat, panel);
    list.append(entry);
  }
  box.append(list);
  // Values the run filled in, with the block that holds each.
  const values = Object.entries(run.result?.values || {});
  if (values.length) {
    const section = el('section', 'results-values');
    section.append(el('h3', 'results-sub', 'Values from this run'));
    const rows = el('ul', 'value-list');
    for (const [name, value] of values) {
      const shown = valueText(value);
      if (!shown) continue;
      const row = el('li');
      const chip = button(name, () => {
        const statement = doc.view?.parsed.statements.find(s => s.name === name);
        if (statement) reveal(spanAt(doc.source, statement.start, statement.end));
      }, 'use-chip');
      chip.title = 'Show ' + name + ' on the canvas';
      setFamily(chip, doc.view?.result.bindings?.[name]?.type);
      const bubble = el('output', 'value-bubble small');
      bubble.append(el('span', 'value-eq', '='), el('span', 'value-text', shown.text));
      if (shown.title) bubble.title = shown.title;
      if (stale || run.outdated?.includes(name)) bubble.dataset.stale = 'true';
      row.append(chip, bubble);
      rows.append(row);
    }
    section.append(rows);
    box.append(section);
  }
  badge.hidden = false;
  badge.textContent = String(run.result.requests.length);
  badge.dataset.state = worst === 'proved' ? 'ready' : ['open', 'error'].includes(worst) ? 'error' : 'warning';
  if (focus) {
    const card = box.querySelector('[data-request="' + focus + '"]');
    scrollInside(byId('panel-results'), card);
    card?.classList.add('flash');
  }
}
function showResults(id) {
  openTab('results', true);
  renderResults(id);
}

function schedule(delay = 240) {
  cancelPreview();
  clearTimeout(timer);
  request?.abort();
  const version = ++generation;
  const current = active;
  host.inert = true;
  host.classList.add('busy');
  setStatus('pending', 'Checking…');
  report.dataset.state = 'pending';
  timer = setTimeout(async () => {
    request = new AbortController();
    const body = {source: current.source, name: current.name};
    try {
      const [parsed, compiled] = await Promise.all([
        api('parse', body, request.signal), api('compile', body, request.signal),
      ]);
      if (version !== generation) return;
      const result = organise(compiled, parsed, current.source);
      current.view = {parsed, result, version};
      // An inert canvas cannot take focus, and mounting may return focus to the edited input.
      host.inert = false;
      host.classList.remove('busy');
      mount(current);
      palette?.setImports(parsed.imports);
      legend();
      showResult(result, parsed);
      renderPractice();
      if (current.recalculate) recalculate(current);
      if (parsed.parse_errors.length) {
        const first = parsed.parse_errors[0];
        setBanner('Line ' + first.source.line + ' could not be read: ' + first.message + ' Blocks after it may be missing.',
          ['Fix in code', () => selectSpan(first.source)]);
      } else setBanner('');
    } catch (error) {
      if (version !== generation || error.name === 'AbortError') return;
      host.replaceChildren();
      byId('dock').replaceChildren();
      host.inert = false;
      host.classList.remove('busy');
      setStatus('offline', error.offline ? 'Checker offline' : 'Check failed');
      report.dataset.state = 'error';
      report.textContent = error.message;
      setBanner(error.message, ['Retry', () => schedule(0)]);
      openTab('code');
    }
  }, delay);
}

// Wiring -------------------------------------------------------------------------------
// Code assistance: completion and hover from the language server's backend-free features.
const codeArea = sourceBox.parentElement;
let metrics = null;
function codeMetrics() {
  if (metrics?.char) return metrics;
  const probe = el('span', 'code-probe', 'M'.repeat(20));
  codeArea.append(probe);
  const style = window.getComputedStyle(sourceBox);
  metrics = {
    char: probe.getBoundingClientRect().width / 20, line: parseFloat(style.lineHeight) || 20,
    top: parseFloat(style.paddingTop) || 12, left: parseFloat(style.paddingLeft) || 14,
  };
  probe.remove();
  return metrics;
}
function caretPosition(index = sourceBox.selectionStart) {
  const before = sourceBox.value.slice(0, index);
  return {line: before.split('\n').length - 1, character: index - (before.lastIndexOf('\n') + 1)};
}
const textIndex = position => sourceBox.value.split('\n').slice(0, position.line).reduce((n, line) => n + line.length + 1, 0) + position.character;
let completion = null;
let completeTimer;
let completeToken = 0;
function closeCompletion() {
  completeToken++;
  completion?.box.remove();
  completion = null;
}
async function requestCompletion() {
  const token = ++completeToken;
  const position = caretPosition();
  const text = sourceBox.value;
  try {
    const result = await api('complete', {source: text, name: active.name, ...position});
    if (token !== completeToken || sourceBox.value !== text || document.activeElement !== sourceBox) return;
    if (result.items.length) showCompletion(result.items, position);
    else closeCompletion();
  } catch { /* completion is optional */ }
}
function showCompletion(items, position) {
  completion?.box.remove();
  const m = codeMetrics();
  const box = el('div', 'complete');
  box.setAttribute('role', 'listbox');
  box.setAttribute('aria-label', 'Suggestions');
  items.forEach((item, i) => {
    const row = button('', () => acceptCompletion(i), 'complete-item');
    row.setAttribute('role', 'option');
    row.addEventListener('pointerdown', event => event.preventDefault());
    row.append(el('span', 'complete-label', item.label));
    if (item.detail) row.append(el('span', 'complete-detail', item.detail));
    if (item.documentation) row.title = item.documentation;
    box.append(row);
  });
  box.style.left = Math.max(4, Math.min(m.left + position.character * m.char - sourceBox.scrollLeft, codeArea.clientWidth - 280)) + 'px';
  box.style.top = m.top + (position.line + 1) * m.line - sourceBox.scrollTop + 2 + 'px';
  codeArea.append(box);
  completion = {box, items, index: 0};
  markCompletion();
}
function markCompletion() {
  const rows = completion.box.querySelectorAll('.complete-item');
  rows.forEach((row, i) => row.setAttribute('aria-selected', String(i === completion.index)));
  if (rows[completion.index]) scrollInside(completion.box, rows[completion.index]);
}
function acceptCompletion(i) {
  const item = completion.items[i];
  closeCompletion();
  sourceBox.setRangeText(item.text, textIndex(item.range.start), textIndex(item.range.end), 'end');
  sourceBox.focus();
  changeSource(sourceBox.value);
  paintCode();
}
let hoverTimer;
let hoverBox = null;
let hoverToken = 0;
function hideHover() {
  hoverToken++;
  hoverBox?.remove();
  hoverBox = null;
}
function markdown(box, text) {
  text.split('```').forEach((part, i) => {
    if (i % 2) { box.append(el('pre', '', part.replace(/^\w*\n/, '').trimEnd())); return; }
    for (const paragraph of part.split(/\n{2,}/).map(t => t.trim()).filter(Boolean)) {
      const node = el('p');
      paragraph.split('`').forEach((bit, j) => node.append(j % 2 ? el('code', '', bit) : bit));
      box.append(node);
    }
  });
}
async function codeHover(x, y) {
  const m = codeMetrics();
  const rect = sourceBox.getBoundingClientRect();
  const line = Math.floor((y - rect.top - m.top + sourceBox.scrollTop) / m.line);
  const character = Math.floor((x - rect.left - m.left + sourceBox.scrollLeft) / m.char);
  const lines = sourceBox.value.split('\n');
  if (line < 0 || line >= lines.length || character < 0 || character >= lines[line].length || completion) return;
  const token = ++hoverToken;
  const text = sourceBox.value;
  const result = await api('hover', {source: text, name: active.name, line, character}).catch(() => null);
  if (token !== hoverToken || !result?.markdown || text !== sourceBox.value) return;
  hoverBox = el('div', 'code-hover');
  hoverBox.setAttribute('role', 'tooltip');
  markdown(hoverBox, result.markdown);
  hoverBox.style.left = Math.max(4, Math.min(x - codeArea.getBoundingClientRect().left - 12, codeArea.clientWidth - 320)) + 'px';
  hoverBox.style.top = m.top + (line + 1) * m.line - sourceBox.scrollTop + 4 + 'px';
  codeArea.append(hoverBox);
}
sourceBox.addEventListener('mousemove', event => {
  clearTimeout(hoverTimer);
  if (hoverBox) hideHover();
  hoverTimer = setTimeout(() => codeHover(event.clientX, event.clientY), 450);
});
sourceBox.addEventListener('mouseleave', () => { clearTimeout(hoverTimer); hideHover(); });
sourceBox.addEventListener('blur', () => setTimeout(closeCompletion, 120));
sourceBox.addEventListener('scroll', () => { closeCompletion(); hideHover(); }, {passive: true});

// Typing in the code panel becomes one undo step per pause, not one per key.
let lastTyped = 0;
sourceBox.addEventListener('input', () => {
  const now = Date.now();
  changeSource(sourceBox.value, now - lastTyped > 900, undefined, {typing: true});
  lastTyped = now;
  hideHover();
  clearTimeout(completeTimer);
  if (/[A-Za-z_.]/.test(sourceBox.value[sourceBox.selectionStart - 1] || '')) completeTimer = setTimeout(requestCompletion, 140);
  else closeCompletion();
});
sourceBox.addEventListener('scroll', syncScroll, {passive: true});
sourceBox.addEventListener('keydown', event => {
  if (completion) {
    const moves = {ArrowDown: 1, ArrowUp: -1};
    if (moves[event.key]) {
      event.preventDefault();
      completion.index = (completion.index + moves[event.key] + completion.items.length) % completion.items.length;
      markCompletion();
      return;
    }
    if (event.key === 'Enter' || event.key === 'Tab') { event.preventDefault(); acceptCompletion(completion.index); return; }
    if (event.key === 'Escape') { event.preventDefault(); closeCompletion(); return; }
  }
  if (event.key === ' ' && event.ctrlKey) { event.preventDefault(); requestCompletion(); return; }
  if (event.key === 'Tab' && !event.shiftKey && !event.metaKey && !event.ctrlKey) {
    event.preventDefault();
    const {selectionStart: start, selectionEnd: end, value} = sourceBox;
    sourceBox.value = value.slice(0, start) + '    ' + value.slice(end);
    sourceBox.setSelectionRange(start + 4, start + 4);
    changeSource(sourceBox.value);
  }
});
picker.addEventListener('change', () => select(picker.value));
byId('compile').addEventListener('click', () => schedule(0));
byId('undo').addEventListener('click', () => history('undo', 'redo'));
byId('historyButton').addEventListener('click', openHistory);
byId('redo').addEventListener('click', () => history('redo', 'undo'));
byId('restoreLesson').addEventListener('click', () => {
  changeSource(active.original);
  toast('Restored the original study', {undo: true});
});
byId('status').addEventListener('click', () => openTab('problems', true));
// On narrow screens the panel is a drawer over the canvas; working on the canvas closes it.
host.addEventListener('pointerdown', () => { if (drawer() && !app.classList.contains('panel-closed')) setPanel(false, false); });
byId('togglePanel').addEventListener('click', () => setPanel(app.classList.contains('panel-closed')));
for (const tab of TABS) {
  const node = byId('tab-' + tab);
  node.addEventListener('click', () => openTab(tab));
  node.addEventListener('keydown', event => {
    const step = event.key === 'ArrowRight' ? 1 : event.key === 'ArrowLeft' ? -1 : 0;
    if (!step) return;
    const next = TABS[(TABS.indexOf(tab) + step + TABS.length) % TABS.length];
    openTab(next);
    byId('tab-' + next).focus();
  });
}
const sideKey = 'statclaim.studio.side.v1';
function setSide(width) {
  const value = Math.round(Math.max(300, Math.min(760, width, window.innerWidth * .6)));
  document.documentElement.style.setProperty('--side', value + 'px');
  return value;
}
try { const stored = Number(window.localStorage.getItem(sideKey)); if (stored) setSide(stored); } catch { /* optional */ }
const resizer = byId('sideResizer');
resizer.addEventListener('pointerdown', event => {
  event.preventDefault();
  resizer.setPointerCapture?.(event.pointerId);
  app.classList.add('resizing');
  const move = e => setSide(window.innerWidth - e.clientX);
  const up = e => {
    app.classList.remove('resizing');
    resizer.removeEventListener('pointermove', move);
    resizer.removeEventListener('pointerup', up);
    try { window.localStorage.setItem(sideKey, String(setSide(window.innerWidth - e.clientX))); } catch { /* optional */ }
  };
  resizer.addEventListener('pointermove', move);
  resizer.addEventListener('pointerup', up);
});
resizer.addEventListener('keydown', event => {
  const step = event.key === 'ArrowLeft' ? 24 : event.key === 'ArrowRight' ? -24 : 0;
  if (!step) return;
  event.preventDefault();
  const current = parseFloat(window.getComputedStyle(document.documentElement).getPropertyValue('--side')) || 380;
  try { window.localStorage.setItem(sideKey, String(setSide(current + step))); } catch { /* optional */ }
});
const zoomKey = 'statclaim.studio.zoom.v1';
function setZoom(value) {
  const zoom = Math.round(Math.max(.5, Math.min(1.6, value)) * 10) / 10;
  host.style.setProperty('--zoom', String(zoom));
  setTimeout(() => drawMinimap(), 50);
  byId('zoomReset').textContent = Math.round(zoom * 100) + '%';
  try { window.localStorage.setItem(zoomKey, String(zoom)); } catch { /* optional */ }
  return zoom;
}
let zoom = 1;
try { zoom = Number(window.localStorage.getItem(zoomKey)) || 1; } catch { /* optional */ }
zoom = setZoom(zoom);
byId('zoomIn').addEventListener('click', () => { zoom = setZoom(zoom + .1); });
byId('zoomOut').addEventListener('click', () => { zoom = setZoom(zoom - .1); });
byId('zoomReset').addEventListener('click', () => { zoom = setZoom(1); });
byId('collapseAll').addEventListener('click', () => canvas?.foldAll(true));
byId('cleanUp').addEventListener('click', () => canvas?.cleanUp());
byId('arrangeFlow').addEventListener('click', () => canvas?.arrangeByFlow());
// Zoom to fit shows the whole study at up to 100%.
function zoomToFit() {
  const size = canvas?.bounds();
  if (!size?.w) return;
  const fit = Math.min(1, (host.clientWidth - 40) / size.w, (host.clientHeight - 110) / size.h);
  zoom = setZoom(Math.floor(Math.max(.5, fit) * 10) / 10);
  host.scrollTo?.(0, 0);
  canvas?.relayout();
}
byId('zoomFit').addEventListener('click', zoomToFit);
// Readings: what each value says in words, under its stack. On by default.
const readingsKey = 'statclaim.studio.readings.v1';
let showReadings = true;
try { showReadings = window.localStorage.getItem(readingsKey) !== 'off'; } catch { /* optional */ }
function paintReadings() {
  host.classList.toggle('hide-readings', !showReadings);
  byId('showReadings').setAttribute('aria-pressed', String(showReadings));
  byId('showReadings').title = showReadings ? 'Hide what each value says in words' : 'Show what each value says in words';
}
paintReadings();
byId('showReadings').addEventListener('click', () => {
  showReadings = !showReadings;
  try { window.localStorage.setItem(readingsKey, showReadings ? 'on' : 'off'); } catch { /* optional */ }
  paintReadings();
  canvas?.relayout();
});
function paintWiresButton() {
  byId('showLinks').setAttribute('aria-pressed', String(showWires));
  byId('showLinks').title = showWires ? 'Hide links between blocks' : 'Show links between blocks';
}
paintWiresButton();
byId('showLinks').addEventListener('click', () => {
  showWires = !showWires;
  try { window.localStorage.setItem(wiresKey, showWires ? 'on' : 'off'); } catch { /* optional */ }
  paintWiresButton();
  canvas?.setWires(showWires);
});
byId('expandAll').addEventListener('click', () => canvas?.foldAll(false));
// Command palette -----------------------------------------------------------------------
// Lean help -----------------------------------------------------------------------
// Where formal proofs can be built, for a studio without Lean: the full studio in a
// Codespace, or StatClaim installed with Lean. `unproved` counts the checks a run left open.
let leanBox = null;
function closeLeanHelp() {
  leanBox?.remove();
  leanBox = null;
}
function openLeanHelp(unproved = 0) {
  closeLeanHelp();
  const links = capabilities.links || {};
  const web = capabilities.where === 'browser';
  const back = el('div', 'lean-back');
  const box = el('section', 'lean-help');
  box.setAttribute('role', 'dialog');
  box.setAttribute('aria-modal', 'true');
  box.setAttribute('aria-labelledby', 'leanHelpTitle');
  const head = el('header', 'lean-head');
  const heading = el('h2', '', 'Formal proofs need Lean');
  heading.id = 'leanHelpTitle';
  const close = button('', closeLeanHelp, 'icon-btn');
  close.setAttribute('aria-label', 'Close');
  close.append(icon('x'));
  head.append(icon('lock', 'icon lean-mark'), heading, close);
  const lead = el('p', 'lean-lead', (unproved ? plural(unproved, 'check') + ' in this study ' + (unproved === 1 ? 'needs' : 'need') + ' a proof. ' : '') +
    (web ? 'This studio runs StatClaim in your browser: it checks studies as you edit, reads them in words, and runs calculations, simulations and cited checks. It cannot run Lean, which builds the formal proofs behind verify(...).'
      : 'Lean is not installed in this checkout, so verify(...) checks cannot build their proofs. Everything else runs as usual.'));
  const ways = el('div', 'lean-ways');
  function way(titleText, steps, recommended) {
    const card = setFamily(el('article', 'lean-way'), 'VerificationResult');
    const hat = el('h3', 'lean-way-hat', titleText);
    if (recommended) hat.append(el('span', 'lean-tag', 'Recommended'));
    const list = el('ol', 'lean-steps');
    for (const step of steps) {
      const item = el('li');
      item.append(...(Array.isArray(step) ? step : [step]));
      list.append(item);
    }
    card.append(hat, list);
    ways.append(card);
  }
  const link = (label, href) => {
    const a = el('a', 'btn small', label);
    a.href = href;
    a.target = '_blank';
    a.rel = 'noopener';
    return a;
  };
  if (links.codespaces) {
    way('The full studio in Codespaces', [
      [el('span', '', 'Save this study. '), button('Save .stat', () => save(), 'btn small')],
      [el('span', '', 'Open StatClaim in a Codespace. The first setup takes a few minutes; then the studio opens in its own tab. '), link('Open Codespaces', links.codespaces)],
      'In that studio, choose Open, pick the saved file and press Run checks.',
    ], web);
  }
  way(web ? 'On your computer' : 'In this checkout', web ? [
    [el('span', '', 'Install uv, elan and Node.js, clone StatClaim and run make setup. '), ...(links.install ? [link('Install steps', links.install)] : [])],
    'Start the studio with uv run --locked python studio/server.py, open the saved file and run its checks.',
  ] : [
    'Run make setup here. It installs Lean and Mathlib, which take several GB.',
    'Restart the studio, then press Run checks.',
  ], !web);
  box.append(head, lead, ways, el('p', 'lean-foot', 'Checks without proofs give the same results everywhere; only verify(...) needs Lean.'));
  back.append(box);
  back.addEventListener('click', event => { if (event.target === back) closeLeanHelp(); });
  back.addEventListener('keydown', event => { if (event.key === 'Escape') { event.stopPropagation(); closeLeanHelp(); } });
  document.body.append(back);
  leanBox = back;
  close.focus();
}
function showLeanChip() {
  const chip = byId('leanChip');
  if (!chip || capabilities.lean) return;
  chip.hidden = false;
  chip.replaceChildren(icon('lock'), el('span', 'lbl', 'Proofs need Lean'));
  chip.title = capabilities.needs_lean || 'Proofs need Lean';
  chip.addEventListener('click', () => openLeanHelp());
}

let commandBox = null;
function commands() {
  const list = [];
  const add = (group, label, run, {hint, keys, family, words} = {}) => list.push({group, label, run, hint, keys, family, words});
  add('Actions', 'Run checks', () => runChecks(), {keys: '⌘↵', hint: canRun(active) ? '' : 'nothing to run, or errors to fix'});
  const counts = blockers(active);
  if (counts && (counts.gaps || counts.errors)) add('Actions', 'Go to the next problem', () => nextProblem(), {keys: 'F8', hint: errorWords(counts)});
  add('Actions', active?.handle ? 'Save to ' + active.name : 'Save', () => save(), {keys: '⌘S'});
  if (fileAccess()) add('Actions', 'Save as…', () => save({as: true}), {keys: '⇧⌘S'});
  if (active && (!active.key.startsWith('local/') || active.practice)) add('Actions', active.practice ? 'Show the practice checklist' : 'Practice this lesson', startPractice, {hint: 'reconnect its values'});
  add('Actions', 'New study', () => newStudy(), {hint: 'from a design'});
  // Every design is a command too, found by its words: "cluster", "interim", "survey".
  for (const d of DESIGNS) {
    const family = DESIGN_FAMILIES.find(f => f.id === d.family);
    add('New study', d.label, () => newStudy({design: d.id}), {hint: family.label, family: family.family, words: d.words + ' new study design ' + d.detail});
  }
  if (active && linkOf.has(active.key) && capabilities.links?.studio) add('Actions', 'Copy link to this study', copyLink, {hint: 'opens it in the web studio', words: 'share cite url address'});
  add('Actions', 'Open a .stat file…', () => typeof window.showOpenFilePicker === 'function' ? openWithPicker() : byId('openFile').click());
  add('Actions', 'Undo', () => history('undo', 'redo'), {keys: '⌘Z', hint: active?.undo.at(-1)?.label});
  add('Actions', 'Show recent edits', openHistory);
  add('Actions', 'Redo', () => history('redo', 'undo'), {keys: '⇧⌘Z'});
  add('Actions', 'Restore original', () => byId('restoreLesson').click());
  add('Actions', 'Recheck with StatClaim', () => schedule(0));
  add('View', 'Arrange by flow', () => canvas?.arrangeByFlow());
  add('View', 'Zoom to fit', zoomToFit);
  add('View', 'Clean up blocks', () => canvas?.cleanUp());
  add('View', 'Collapse all', () => canvas?.foldAll(true));
  add('View', 'Expand all', () => canvas?.foldAll(false));
  add('View', showWires ? 'Hide links between blocks' : 'Show links between blocks', () => byId('showLinks').click());
  add('View', showReadings ? 'Hide readings' : 'Show readings', () => byId('showReadings').click(), {hint: 'what each value says in words'});
  add('View', 'Toggle side panel', () => byId('togglePanel').click());
  for (const tab of TABS) add('View', 'Show ' + tab, () => openTab(tab, true));
  add('View', 'Zoom in', () => byId('zoomIn').click());
  add('View', 'Zoom out', () => byId('zoomOut').click());
  add('View', 'Reset zoom', () => byId('zoomReset').click());
  (active?.view?.parsed.statements || []).forEach((statement, i) => {
    if (statement.name) add('Go to', statement.name, () => canvas?.focusStatement(i), {hint: human(statement.expression.label || statement.expression.kind)});
  });
  for (const constructors of [...Object.values(catalog.modules), catalog.operations]) {
    for (const [name, sig] of Object.entries(constructors)) {
      if (list.some(item => item.group === 'Add a block' && item.label === human(name))) continue;
      add('Add a block', human(name), () => canvas?.arm({...sig, name, module: Object.keys(catalog.modules).find(m => catalog.modules[m][name] === sig)}),
        {hint: sig.result, family: familyOf(sig.result)});
    }
  }
  for (const option of picker.querySelectorAll('option')) {
    add('Open', option.textContent, () => select(option.value), {hint: option.parentElement.label});
  }
  return list;
}
function closeCommands() {
  commandBox?.remove();
  commandBox = null;
}
function openCommands() {
  if (!catalog) return;
  closeCommands();
  const back = el('div', 'cmdk-back');
  const box = el('div', 'cmdk');
  box.setAttribute('role', 'dialog');
  box.setAttribute('aria-label', 'Command palette');
  const field = el('label', 'pop-search cmdk-search');
  field.append(icon('search'));
  const input = el('input');
  input.type = 'search';
  input.placeholder = 'Run a command, go to a value, add a block or open a study';
  input.setAttribute('aria-label', input.placeholder);
  field.append(input);
  const list = el('div', 'cmdk-list');
  list.setAttribute('role', 'listbox');
  box.append(field, list, el('p', 'cmdk-foot', '↑ ↓ to move · Enter to choose · Esc to close'));
  back.append(box);
  document.body.append(back);
  commandBox = back;
  const all = commands();
  let shown = [];
  let index = 0;
  const choose = item => { closeCommands(); item.run(); };
  function paint() {
    const words = input.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
    const score = item => {
      const text = (item.label + ' ' + item.group + ' ' + (item.hint || '') + ' ' + (item.words || '')).toLowerCase();
      if (!words.every(word => text.includes(word))) return -1;
      // Designs wait for a word, so the first view stays short.
      if (!words.length && item.group === 'New study') return -1;
      const label = item.label.toLowerCase();
      return (label.startsWith(words[0] || '') ? 3 : 0) + (label.includes(words.join(' ')) ? 2 : 0) + (item.group === 'Actions' ? 1 : 0);
    };
    shown = all.map(item => [score(item), item]).filter(([value]) => value >= 0)
      .sort((a, b) => b[0] - a[0]).slice(0, words.length ? 40 : 18).map(([, item]) => item);
    if (!words.length) shown.sort((a, b) => ['Actions', 'Go to', 'View', 'Add a block', 'Open'].indexOf(a.group) - ['Actions', 'Go to', 'View', 'Add a block', 'Open'].indexOf(b.group));
    index = Math.min(index, Math.max(0, shown.length - 1));
    list.replaceChildren();
    let group = '';
    shown.forEach((item, i) => {
      if (item.group !== group) { group = item.group; list.append(el('h4', 'opt-head', group)); }
      const row = button('', () => choose(item), 'cmdk-item');
      row.setAttribute('role', 'option');
      row.setAttribute('aria-selected', String(i === index));
      if (item.family) {
        const dot = el('span', 'legend-swatch');
        dot.dataset.family = item.family;
        row.append(dot);
      }
      row.append(el('span', 'cmdk-label', item.label));
      if (item.hint) row.append(el('span', 'cmdk-hint', item.hint));
      if (item.keys) row.append(el('kbd', '', item.keys));
      row.addEventListener('mousemove', () => { if (index !== i) { index = i; mark(); } });
      list.append(row);
    });
    if (!shown.length) list.append(el('p', 'pop-empty', 'Nothing matches.'));
  }
  function mark() {
    list.querySelectorAll('.cmdk-item').forEach((row, i) => row.setAttribute('aria-selected', String(i === index)));
    const row = list.querySelectorAll('.cmdk-item')[index];
    if (row) scrollInside(list, row);
  }
  input.addEventListener('input', () => { index = 0; paint(); });
  input.addEventListener('keydown', event => {
    if (event.key === 'ArrowDown') { event.preventDefault(); index = Math.min(shown.length - 1, index + 1); mark(); }
    else if (event.key === 'ArrowUp') { event.preventDefault(); index = Math.max(0, index - 1); mark(); }
    else if (event.key === 'Enter' && shown[index]) { event.preventDefault(); choose(shown[index]); }
    else if (event.key === 'Escape') { event.preventDefault(); closeCommands(); }
  });
  back.addEventListener('pointerdown', event => { if (event.target === back) closeCommands(); });
  paint();
  input.focus();
}

function download() {
  if (!active) return;
  const link = document.createElement('a');
  const url = URL.createObjectURL(new Blob([active.source], {type: 'text/plain;charset=utf-8'}));
  link.href = url;
  link.download = active.name;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
  toast('Downloaded ' + active.name);
}
byId('download').addEventListener('click', () => save());
byId('runChecks').addEventListener('click', () => runChecks());
byId('commandButton').addEventListener('click', () => openCommands());
document.addEventListener('keydown', event => {
  const key = event.key.toLowerCase();
  const mod = event.metaKey || event.ctrlKey;
  if (mod && key === 'k') { event.preventDefault(); commandBox ? closeCommands() : openCommands(); return; }
  if (mod && key === 's') { event.preventDefault(); save({as: event.shiftKey}); return; }
  if (mod && key === 'o' && typeof window.showOpenFilePicker === 'function') { event.preventDefault(); openWithPicker(); return; }
  if (mod && event.key === 'Enter') { event.preventDefault(); runChecks(); return; }
  if (event.key === 'F8') { event.preventDefault(); nextProblem(event.shiftKey ? -1 : 1); return; }
  if (event.target.closest?.('input, textarea, select, [contenteditable]')) return;
  if (mod && key === 'z') { event.preventDefault(); event.shiftKey ? history('redo', 'undo') : history('undo', 'redo'); }
  else if (mod && key === 'y') { event.preventDefault(); history('redo', 'undo'); }
  else if (event.key === '/' && palette) { event.preventDefault(); palette.search.focus(); }
});

// In the web studio, StatClaim starts loading in this browser at once, while the page builds.
if (where === 'browser') {
  prepare();
  let starting = false;
  onState((state, detail) => {
    if (state === 'starting') {
      starting = true;
      setBanner('Starting StatClaim in this browser. The first visit downloads about 12 MB; later visits start sooner.', null, 'info');
    } else if (state === 'ready' && starting) {
      starting = false;
      setBanner(null);
    } else if (state === 'failed') {
      setStatus('offline', 'StatClaim stopped');
      setBanner('StatClaim could not start in this browser (' + detail + '). Try a recent Chrome, Edge, Firefox or Safari, or the full studio in Codespaces.',
        capabilities.links?.codespaces ? ['Open Codespaces', () => window.open(capabilities.links.codespaces, '_blank', 'noopener')] : null);
    }
  });
}

try {
  try {
    const stored = window.localStorage.getItem(panelKey);
    setPanel(!drawer() && stored !== 'closed', false);
  } catch { setPanel(true); }
  const [manifest, tutorials, examples, paper, replication, found] = await Promise.all(
    ['blocks', 'tutorials', 'examples', 'paper', 'replication', 'capabilities'].map(name => api(name)));
  catalog = manifest;
  capabilities = found;
  showLeanChip();
  for (const constructors of [...Object.values(catalog.modules), catalog.operations]) {
    for (const [name, sig] of Object.entries(constructors)) {
      callFamily.set(name, familyOf(sig.result));
      if (!signatures.has(name)) signatures.set(name, sig);
    }
  }
  palette = mountPalette(byId('library'), catalog, {
    arm: sig => canvas?.arm(sig),
    grab: (sig, event, element) => canvas?.grab(sig, event, element),
    hover: sig => showHelp(sig, true),
    clearHint: () => armedSig ? canvas?.disarm() : canvas?.select(null),
  });
  renderHelp(null);
  const myStudiesGroup = group('My studies');
  const tutorialGroup = group('Tutorials');
  const exampleGroup = group('Examples');
  const paperGroup = group('Paper');
  const replicationGroup = group('Replication');
  const stem = name => name.replace(/\.stat$/, '');
  for (const doc of tutorials) {
    register(doc.name, doc.name, doc.source, tutorialGroup);
    linkStudy(doc.name, 'tutorial/' + stem(doc.name), 'examples/tutorial/' + stem(doc.name));
  }
  for (const doc of examples) {
    register('example/' + doc.name, doc.name, doc.source, exampleGroup);
    linkStudy('example/' + doc.name, 'example/' + stem(doc.name), 'examples/' + stem(doc.name));
  }
  // The programs the StatClaim article shows, from examples/paper.
  for (const doc of paper) {
    register('paper/' + doc.name, doc.name, doc.source, paperGroup);
    linkStudy('paper/' + doc.name, 'paper/' + stem(doc.name), 'examples/paper/' + stem(doc.name));
  }
  // Case studies and cross-checks, from replication/<folder>/; each is named <folder>/<file>.stat.
  for (const doc of replication) {
    register('replication/' + doc.name, doc.name.replace('/', '_'), doc.source, replicationGroup);
    linkStudy('replication/' + doc.name, stem(doc.name), 'replication/' + stem(doc.name));
  }
  if (!paper.length) paperGroup.remove();
  if (!replication.length) replicationGroup.remove();
  byId('newDoc').addEventListener('click', () => newStudy());
  byId('openFile').addEventListener('change', async event => {
    const field = event.target;
    const file = field.files[0];
    if (!file) return;
    try {
      const source = await file.text();
      documents.get(addLocal(file.name, source)).saved = source;
      controls();
      toast('Opened ' + file.name);
    } catch (error) { toast('Could not open the file. ' + error.message); }
    finally { field.value = ''; }
  });
  // With file access, Open keeps a link to the file so Save can write back to it.
  byId('openFile').parentElement.addEventListener('click', event => {
    if (typeof window.showOpenFilePicker !== 'function') return;
    event.preventDefault();
    openWithPicker();
  });
  for (const id of ['lesson', 'newDoc', 'openFile', 'download', 'compile', 'source']) byId(id).disabled = false;
  byId('lesson').title = 'StatClaim ' + catalog.version;
  const recovered = recoverDrafts(myStudiesGroup);
  // A link opens its study, over the one open last time.
  const wanted = requestedLink();
  const linked = wanted && studyLinks.get(wanted);
  if (linked) select(linked);
  else if (documents.has(recovered.selected)) select(recovered.selected);
  else if (tutorials.length) select(tutorials[0].name);
  else addLocal('study.stat', '');
  if (wanted && !linked) toast('No study here has the link ' + JSON.stringify(wanted) + '; it may have been renamed.');
  else if (linked && active.source !== active.original) toast('This is your edited copy of ' + title(active.name) + '. Restore original shows it as published.');
  // A new visit, not a reload, says that unsaved edits came back.
  let returning = false;
  try { returning = !window.sessionStorage.getItem(visitKey); window.sessionStorage.setItem(visitKey, '1'); } catch { /* optional */ }
  if (returning && recovered.edited) toast('Restored unsaved edits to ' + plural(recovered.edited, 'study', 'studies') + ' from your last visit.');
} catch (error) {
  setStatus('offline', 'Checker offline');
  report.dataset.state = 'error';
  if (where === 'browser') {
    report.textContent = 'Could not load the web studio. Reload the page. ' + error.message;
    setBanner('Could not load the web studio. Reload the page.');
  } else {
    report.textContent = 'Could not load the editor. Restart studio/server.py from this checkout and reload. ' + error.message;
    setBanner('Could not reach the StatClaim checker. Start the studio server with .venv/bin/python studio/server.py, then reload.');
  }
}
