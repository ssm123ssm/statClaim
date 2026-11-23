// The study canvas. Every edit patches the original source through Python parser spans.
import { el, button, human, icon, iconButton, familyOf, setFamily, codeTitle, plural, messageBlock, outcome, outcomeBadge, headline, valueText, scrubber, certStamp, scrollInside, fixBox, keyShape, keyGlyph, SHAPES, FAMILIES, derivationView } from './ui.js';
import { miniBlock, moduleTitle } from './palette.js';
import { FAMILIES as DESIGN_FAMILIES, DESIGNS } from './designs.js';
import { glyph } from './wizard.js';

// The Python parser counts Unicode code points. All edits use its half-open spans.
export function applyEdits(source, edits) {
  const chars = Array.from(source);
  const result = [];
  let end = chars.length;
  for (const edit of [...edits].sort((a, b) => b.start - a.start || b.end - a.end)) {
    if (edit.end > end || edit.start < 0 || edit.start > edit.end) throw Error('Invalid source edit');
    result.push(chars.slice(edit.end, end).join(''), edit.text);
    end = edit.start;
  }
  result.push(chars.slice(0, end).join(''));
  return result.reverse().join('');
}

function walk(node, visit) {
  visit(node);
  for (const child of node.children || []) walk(child, visit);
}

const ident = /^[A-Za-z_][A-Za-z_0-9]*$/;
const number = /^-?\d+(?:\.\d+|\s*\/\s*-?\d+)?$/;
const numeric = type => ['level', 'number', 'exact number', 'integer'].includes(type);
const NUMBER_HINT = 'Use a whole number, a decimal or a fraction such as 1/20.';
const esc = text => globalThis.CSS?.escape ? globalThis.CSS.escape(text) : String(text).replace(/["\\]/g, '\\$&');
function choice(label, value) {
  const node = document.createElement('option');
  node.textContent = label;
  node.value = value;
  return node;
}
// New values take the names the tutorials use for their type.
const NAME_FOR = {
  Model: 'study', OneArmModel: 'study', TwoStageModel: 'study', OutcomeModel: 'study',
  StudyDesign: 'design', Hypothesis: 'null', OutcomeNull: 'null', SharpNull: 'null',
  Analysis: 'analysis', CitedAnalysis: 'analysis', RandomisationAnalysis: 'analysis',
  OneSampleAnalysis: 'analysis', TwoStageAnalysis: 'analysis', Family: 'family', ComposedFamily: 'family',
  TypeIClaim: 'claim', FamilywiseClaim: 'claim', ResultClaim: 'claim', PlanningClaim: 'claim', IntervalClaim: 'claim',
  VerificationResult: 'verification', CalculationResult: 'calculation', Observation: 'data',
  CrossSectionalStudy: 'survey', CohortStudy: 'cohort', CaseControlStudy: 'study',
  AssociationNull: 'null', AssociationAnalysis: 'analysis', AssociationTable: 'table',
  MatchedStudy: 'paired', MatchedAnalysis: 'analysis', MatchedPairs: 'pairs',
  PersonTimeStudy: 'cohort', RateAnalysis: 'analysis', ObservedEvents: 'events',
  CitedAssociation: 'analysis',
};
const QUICK = {level: ['1/20', '1/40', '0.025'], integer: ['1', '50', '100'], number: ['0', '1/10', '1'], 'exact number': ['0', '1/10', '1']};

let teardown = null;
// The canvas is rebuilt on every edit; a value bubble pops in only when its value first shows or changes.
const shownValues = new Map();
// Certificates whose stamp has already landed, so a redraw does not stamp them again.
const stampedChecks = new Set();

export function mountDocument(host, options) {
  teardown?.();
  const life = new AbortController();
  const listen = (target, type, handler, extra = {}) => target.addEventListener(type, handler, {...extra, signal: life.signal});
  const {source, statements = [], imports = [], modules = {}, operations = {}, objects = {}, onChange} = options;
  const bindings = options.bindings || {};
  const folded = options.folded || new Set();
  const chars = Array.from(source);
  const slice = (start, end) => chars.slice(start, end).join('');
  const declarations = statements.filter(s => s.name);
  const allCalls = new Map();
  const library = [];
  // Prefer a module the study already uses when several modules share a constructor.
  for (const module of new Set([...imports, ...Object.keys(modules)])) {
    for (const [name, sig] of Object.entries(modules[module] || {})) {
      if (allCalls.has(name)) continue;
      const entry = {...sig, name, module};
      library.push(entry);
      allCalls.set(name, entry);
    }
  }
  for (const [name, sig] of Object.entries(operations)) {
    const entry = {...sig, name};
    allCalls.set(name, entry);
    library.push(entry);
  }
  const sockets = [];
  const stacks = [];
  const known = new Map();
  const users = new Map();
  statements.forEach((s, i) => walk(s.expression, n => {
    if (n.kind !== 'Reference') return;
    if (!users.has(n.label)) users.set(n.label, new Set());
    users.get(n.label).add(i);
  }));
  let pop = null;
  let popAnchor = null;
  let bubble = null;
  let armed = null;
  let banner = null;
  let dragging = null;
  let hint = null;
  let overSlot = null;
  let nopeSlot = null;
  // Stack positions live outside the .stat file. Without a layout, stacks form a column in file order.
  let layout = options.layout ? {...options.layout} : null;
  let board = null;
  let zTop = 1;
  const PAD = 28;
  const GAP = 26;
  const blockInfo = new WeakMap();
  let wiresOn = Boolean(options.wires);
  // The selected stack. The palette hints the blocks that take its value, and open inputs
  // that take it are marked, from the fits Python found by building each block with it.
  let selected = options.selected || null;
  let selectedFits = null;
  let hoverCard = null;
  let wireLayer = null;
  const keyOf = s => s.name || 'check:' + slice(s.expression.start, s.expression.end).replace(/\s+/g, ' ');

  const resolve = sig => {
    if (!sig?.module || imports.includes(sig.module)) return sig;
    const used = imports.find(m => modules[m]?.[sig.name]);
    return used ? {...sig, module: used} : sig;
  };
  function typeOf(node) {
    if (node.kind === 'Call') return allCalls.get(node.label)?.result;
    if (node.kind === 'Literal') return node.literal.startsWith('"') ? 'string' : /^-?\d+$/.test(node.literal) ? 'integer' : 'exact number';
    if (node.kind === 'Reference') return bindings[node.label]?.type || known.get(node.label);
    if (node.kind === 'ListExpr') return 'list';
    if (node.kind === 'FieldAccess') return fields(node.children[0])[node.label.slice(1)];
  }
  function fields(node) {
    if (node.kind === 'Reference' && bindings[node.label]?.fields) return bindings[node.label].fields;
    const type = typeOf(node);
    const inner = type?.match(/^Option\[(.*)\]$/)?.[1];
    return objects[inner || type]?.fields || {};
  }
  function accepts(type, expected, binding, socket) {
    if (!expected) return true;
    if (binding && socket) {
      return binding.accepts?.[socket.sig.module || '']?.[socket.sig.name]?.includes(socket.param) || false;
    }
    const accepted = socket?.sig.accepted_results?.[socket.param];
    if (accepted?.length) return accepted.includes(type);
    return type === expected || (numeric(expected) && numeric(type) && (expected !== 'integer' || type === 'integer'));
  }
  function available(at, expected, socket) {
    return declarations.filter(s => s.end <= at && (!socket || Object.hasOwn(bindings, s.name)) &&
      accepts(bindings[s.name]?.type || known.get(s.name), expected, bindings[s.name], socket));
  }
  // The registry lists the fixed values of string inputs; each becomes a dropdown.
  const enumeration = context => {
    if (!context?.sig) return null;
    const listed = context.sig.choices?.[context.param];
    if (listed?.length) {
      const meanings = options.parameter_choices?.[context.param] || {};
      return Object.fromEntries(listed.map(value => [value, meanings[value] || '']));
    }
    return options.enumerations?.[context.sig.name + ' ' + context.param];
  };

  // Popovers ---------------------------------------------------------------
  function close(restore) {
    hideBubble();
    if (!pop) return;
    pop.remove();
    pop = null;
    if (restore && popAnchor?.isConnected) popAnchor.focus();
  }
  function place(node, anchor) {
    if (!node.isConnected || !anchor.isConnected) return;
    node.style.maxHeight = '';
    const rect = anchor.getBoundingClientRect();
    const width = node.offsetWidth || 320;
    const head = node.querySelector('.pop-head')?.offsetHeight || 0;
    const natural = Math.min(window.innerHeight * .7, head + (node.querySelector('.pop-body')?.scrollHeight || 0)) || 240;
    const below = window.innerHeight - rect.bottom - 14;
    const aboveRoom = rect.top - 14;
    // Open upwards when the menu would not fit below and there is more room above.
    const above = natural > below && aboveRoom > below;
    const room = Math.max(160, above ? aboveRoom : below);
    const height = Math.min(natural, room);
    node.dataset.side = above ? 'above' : 'below';
    node.style.maxHeight = room + 'px';
    node.style.left = Math.max(8, Math.min(rect.left, window.innerWidth - width - 8)) + 'px';
    const top = above ? rect.top - height - 6 : rect.bottom + 6;
    node.style.top = Math.max(8, Math.min(top, window.innerHeight - height - 8)) + 'px';
  }
  function open(anchor, heading, {cls = '', subtitle, family} = {}) {
    close();
    pop = el('section', 'pop ' + cls);
    pop.setAttribute('role', 'dialog');
    pop.setAttribute('aria-label', heading);
    const head = el('header', 'pop-head');
    if (family) head.dataset.family = family;
    const titles = el('div', 'pop-titles');
    titles.append(el('strong', 'pop-title', heading));
    if (subtitle) titles.append(el('span', 'pop-sub', subtitle));
    head.append(titles, iconButton('x', 'Close', () => close(true), 'icon-btn pop-close'));
    const body = el('div', 'pop-body');
    pop.append(head, body);
    host.append(pop);
    popAnchor = anchor;
    const current = pop;
    current.addEventListener('keydown', event => {
      if (event.key === 'Escape') { event.stopPropagation(); close(true); }
    });
    queueMicrotask(() => { if (pop === current) place(current, anchor); });
    return body;
  }
  listen(document, 'pointerdown', event => {
    if (pop && !pop.contains(event.target) && !popAnchor?.contains(event.target)) close();
  }, {capture: true});
  listen(window, 'resize', () => { if (pop) place(pop, popAnchor); });
  listen(host, 'scroll', () => { if (pop) place(pop, popAnchor); if (bubble) placeBubble(); }, {passive: true});

  function menuItem(parent, label, iconName, action, {disabled, note, danger} = {}) {
    const item = button('', action, 'menu-item' + (danger ? ' danger' : ''));
    item.append(icon(iconName), el('span', 'menu-label', label));
    if (note) item.append(el('span', 'menu-note', note));
    item.disabled = Boolean(disabled);
    parent.append(item);
    return item;
  }
  function showBubble(anchor, message, tone = 'error') {
    hideBubble();
    bubble = el('div', 'bubble bubble-' + tone, message);
    bubble.setAttribute('role', tone === 'error' ? 'alert' : 'status');
    bubble.anchor = anchor;
    host.append(bubble);
    placeBubble();
  }
  function placeBubble() {
    if (!bubble?.anchor?.isConnected) return hideBubble();
    const rect = bubble.anchor.getBoundingClientRect();
    bubble.style.left = Math.max(8, Math.min(rect.left, window.innerWidth - 300)) + 'px';
    bubble.style.top = rect.bottom + 8 + 'px';
  }
  function hideBubble() { bubble?.remove(); bubble = null; }

  // Editing ----------------------------------------------------------------
  function edit(edits, module) {
    const primary = edits[0];
    if (module && !imports.includes(module)) edits.push(useEdit(module));
    // An edit made from the canvas returns focus to what it changed once the canvas is redrawn.
    const focused = document.activeElement;
    const refocus = !focused || focused === document.body || host.contains(focused);
    close();
    disarm();
    // Report where the main edit lands in the new source so the editor can highlight it.
    let shift = 0;
    for (const other of edits) {
      if (other !== primary && other.end <= primary.start) shift += Array.from(other.text).length - (other.end - other.start);
    }
    const start = primary.start + shift;
    onChange(applyEdits(source, edits), {start, end: start + Array.from(primary.text).length}, {refocus});
  }
  const change = (start, end, text, module) => edit([{start, end, text}], module);
  // New modules go after the existing `use` lines, so the file's opening comment stays first.
  function useEdit(module) {
    const last = (options.uses || []).at(-1);
    return last ? {start: last.end, end: last.end, text: '\nuse ' + module} : {start: headerEnd, end: headerEnd, text: 'use ' + module + '\n'};
  }
  const stamp = (node, text) => ({start: node.start, end: node.end, text});
  function freshName(base) {
    let name = base;
    let index = 2;
    while (declarations.some(s => s.name === name) || Object.hasOwn(operations, name)) name = base + '_' + index++;
    return name;
  }
  function seed(type, at, param, sig) {
    const previous = available(at, type, {sig, param}).at(-1);
    if (previous) return previous.name;
    if (numeric(type)) return type === 'level' ? '0.05' : '1';
    if (type === 'string') return JSON.stringify(sig?.choices?.[param]?.[0] ?? '');
    if (type === 'list') return '[]';
    return holeName(param);
  }
  // An empty input is an undeclared name the canvas draws as a gap.
  function holeName(param) {
    let name = 'choose_' + (param && ident.test(param) ? param : 'value');
    while (declarations.some(s => s.name === name)) name += '_';
    return name;
  }
  const isHole = node => node?.kind === 'Reference' && node.label.startsWith('choose_') && !declarations.some(s => s.name === node.label);
  function callValue(sig, at, supplied = {}) {
    const args = Object.entries(sig.parameters || {}).filter(([p]) => Object.hasOwn(supplied, p) || !(sig.optional || []).includes(p));
    return sig.name + '(' + args.map(([p, t]) => p + '=' + (supplied[p] ?? seed(t, at, p, sig))).join(', ') + ')';
  }
  function addDeclaration(value, module, point) {
    const stem = value.match(/^([A-Za-z_]\w*)\(/)?.[1] || 'value';
    const name = freshName(NAME_FOR[allCalls.get(stem)?.result] || (Object.hasOwn(operations, stem) ? stem + '_result' : stem));
    const prefix = source && !source.endsWith('\n') ? '\n' : '';
    if (point) placeNew(name, point);
    change(chars.length, chars.length, prefix + 'let ' + name + ' = ' + value + '\n', module);
  }
  function addCheck(name, point) {
    const text = callValue(allCalls.get(name), chars.length);
    const prefix = source && !source.endsWith('\n') ? '\n' : '';
    if (point) placeNew('check:' + text, point);
    change(chars.length, chars.length, prefix + text + '\n');
  }
  function replacementCall(sig, at, previous) {
    if (previous?.kind === 'Reference') {
      previous = declarations.find(s => s.name === previous.label && s.end <= at)?.expression;
    }
    if (previous?.kind !== 'Call') return callValue(sig, at);
    if (previous.label === sig.name) return slice(previous.start, previous.end);
    const old = allCalls.get(previous.label);
    const supplied = {};
    for (const [i, child] of previous.children.entries()) {
      const p = child.argument || Object.keys(old?.parameters || {})[i];
      if (p && sig.parameters[p] && old?.input_kinds?.[p] === sig.input_kinds?.[p]) supplied[p] = slice(child.start, child.end);
    }
    for (const p of Object.keys(sig.parameters)) {
      if (!Object.hasOwn(supplied, p) && !(sig.optional || []).includes(p)) supplied[p] = holeName(p);
    }
    return callValue(sig, at, supplied);
  }
  function appendChild(node, text, module) {
    const children = node.children || [];
    const end = node.end - 1;
    const last = children.at(-1);
    const tail = last ? slice(last.end, end).replace(/#[^\n]*/g, '') : '';
    // Insert after trailing comments, retaining the original comma if one exists.
    const prefix = last && !tail.includes(',') ? ', ' : '';
    change(end, end, prefix + text, module);
  }
  function removeChild(node, index) {
    edit(removalEdits(node, index));
  }
  function removalEdits(node, index) {
    const child = node.children[index];
    const before = index ? node.children[index - 1].end : node.start;
    const masked = slice(before, child.start).replace(/#[^\n]*/gu, m => ' '.repeat(Array.from(m).length));
    const edits = [stamp(child, '')];
    if (child.argument) {
      const name = masked.match(/([A-Za-z_][A-Za-z_0-9]*)\s*=\s*$/);
      if (name) {
        const start = before + Array.from(masked.slice(0, name.index)).length;
        edits.push({start, end: start + child.argument.length, text: ''});
        const equals = before + Array.from(masked.slice(0, masked.lastIndexOf('='))).length;
        edits.push({start: equals, end: equals + 1, text: ''});
      }
    }
    const after = slice(child.end, node.children[index + 1]?.start ?? node.end - 1).replace(/#[^\n]*/gu, m => ' '.repeat(Array.from(m).length));
    const comma = after.indexOf(',');
    const preceding = masked.lastIndexOf(',');
    const offset = comma >= 0 ? child.end + Array.from(after.slice(0, comma)).length :
      index && preceding >= 0 ? before + Array.from(masked.slice(0, preceding)).length : -1;
    if (offset >= 0) edits.push({start: offset, end: offset + 1, text: ''});
    return edits;
  }
  function extractDeclaration(node, at) {
    const name = freshName(node.kind === 'Call' ? NAME_FOR[allCalls.get(node.label)?.result] || node.label : 'items');
    const owner = stacks.find(e => e.s.start === at);
    const point = owner && near(owner.s);
    if (point) placeNew(name, point);
    edit([{start: at, end: at, text: 'let ' + name + ' = ' + slice(node.start, node.end) + '\n'}, stamp(node, name)]);
    options.onToast?.('Made a shared value named ' + name);
  }

  // Comments directly above a statement are its note. The file's opening comment is its description.
  const headerEnd = (() => {
    const lines = source.split('\n');
    let count = 0;
    let offset = 0;
    while (count < lines.length - 1 && /^\s*#/.test(lines[count])) offset += Array.from(lines[count++]).length + 1;
    const next = lines[count] ?? '';
    return count && (!next.trim() || /^\s*use\b/.test(next)) ? offset : 0;
  })();
  const boundaries = [headerEnd, ...(options.uses || []).map(u => u.end), ...statements.map(s => s.end)];
  function noteRange(s) {
    const previous = Math.max(0, ...boundaries.filter(end => end <= s.start));
    const lines = slice(previous, s.start).split('\n');
    const indent = Array.from(lines.at(-1)).length;
    const notes = [];
    let i = lines.length - 2;
    while (i >= 0 && /^\s*#/.test(lines[i])) notes.unshift(lines[i--].trim().replace(/^#\s?/, ''));
    const lineStart = s.start - indent;
    if (!notes.length) return {start: lineStart, end: lineStart, text: ''};
    const start = previous + Array.from(lines.slice(0, i + 1).join('\n')).length + (i >= 0 ? 1 : 0);
    return {start, end: lineStart, text: notes.join('\n')};
  }
  function headerNote() {
    const text = slice(0, headerEnd).split('\n').filter(line => line.trim()).map(line => line.trim().replace(/^#\s?/, '')).join('\n');
    return {start: 0, end: headerEnd, text};
  }
  // Each line of a note becomes a # comment; a blank line stays, as a bare #, between paragraphs.
  const commentText = text => {
    const lines = text.split('\n').map(line => line.trim());
    while (lines.length && !lines[0]) lines.shift();
    while (lines.length && !lines.at(-1)) lines.pop();
    return lines.map(line => (line ? '# ' + line : '#') + '\n').join('');
  };
  // Comments are wrapped to suit a text editor; a note reads them as paragraphs. A blank
  // comment line starts a paragraph, and a list item ("- ", "1. ") starts a line.
  const prose = text => {
    const out = [];
    for (const line of text.split('\n').map(part => part.trim())) {
      if (!line) { if (out.length && out.at(-1)) out.push(''); }
      else if (!out.length || !out.at(-1) || /^([-*•]|\d+[.)])\s/.test(line)) out.push(line);
      else out[out.length - 1] += ' ' + line;
    }
    while (out.length && !out.at(-1)) out.pop();
    return out.join('\n');
  };
  function editNote(anchor, range, heading) {
    const body = open(anchor, heading, {cls: 'note-pop', subtitle: 'Saved as # comments in the .stat file'});
    const form = el('form', 'note-form');
    const area = el('textarea', 'note-input');
    area.value = range.text;
    area.rows = 3;
    area.setAttribute('aria-label', heading);
    const actions = el('div', 'pop-actions');
    const save = el('button', 'btn primary', 'Save note');
    save.type = 'submit';
    actions.append(save);
    if (range.text) actions.append(button('Remove note', () => change(range.start, range.end, ''), 'btn ghost danger'));
    form.append(area, actions);
    body.append(form);
    form.addEventListener('submit', event => {
      event.preventDefault();
      const text = commentText(area.value);
      if (range.text || text) change(range.start, range.end, text);
      else close();
    });
    area.addEventListener('keydown', event => {
      if (event.key === 'Enter' && (event.metaKey || event.ctrlKey)) {
        event.preventDefault();
        if (form.requestSubmit) form.requestSubmit(); else save.click();
      }
    });
    area.focus();
  }

  // Choosers ---------------------------------------------------------------
  function options_(body) {
    const list = el('div', 'pop-list');
    list.setAttribute('role', 'listbox');
    body.append(list);
    return list;
  }
  function group(list, label) {
    const box = el('div', 'opt-group');
    box.setAttribute('role', 'group');
    box.setAttribute('aria-label', label);
    list.append(el('h4', 'opt-head', label), box);
    return box;
  }
  function option(box, label, pick, {family, kind = 'plain', hint} = {}) {
    const item = button('', pick, 'opt opt-' + kind);
    item.setAttribute('role', 'option');
    const text = el('span', 'opt-label', label);
    if (family) item.dataset.family = family;
    item.append(text);
    if (family && (kind === 'ref' || kind === 'field')) keyed(item, family);
    if (hint) item.append(el('span', 'opt-hint', hint));
    box.append(item);
    return item;
  }
  function navigable(list, search) {
    const visible = () => [...list.querySelectorAll('.opt')].filter(o => !o.hidden && !o.closest('[hidden]'));
    list.addEventListener('keydown', event => {
      const items = visible();
      const index = items.indexOf(document.activeElement);
      if (event.key === 'ArrowDown') { event.preventDefault(); items[Math.min(items.length - 1, index + 1)]?.focus(); }
      if (event.key === 'ArrowUp') { event.preventDefault(); (index <= 0 ? search : items[index - 1])?.focus(); }
    });
    search?.addEventListener('keydown', event => {
      if (event.key === 'ArrowDown') { event.preventDefault(); visible()[0]?.focus(); }
      if (event.key === 'Enter') { event.preventDefault(); visible()[0]?.click(); }
    });
  }
  function filterable(list, search, extra) {
    const empty = el('p', 'pop-empty', 'Nothing here matches.');
    empty.hidden = true;
    list.after(empty);
    search.addEventListener('input', () => {
      const query = search.value.trim().toLowerCase().replaceAll('_', ' ');
      let shown = 0;
      for (const box of list.querySelectorAll('.opt-group')) {
        if (box.dataset.dynamic) continue;
        let any = false;
        for (const item of box.querySelectorAll('.opt')) {
          item.hidden = !(item.textContent + ' ' + box.getAttribute('aria-label')).toLowerCase().replaceAll('_', ' ').includes(query);
          if (!item.hidden) { any = true; shown++; }
        }
        box.hidden = !any;
        box.previousElementSibling.hidden = !any;
      }
      shown += extra?.(search.value.trim()) || 0;
      empty.hidden = shown > 0;
    });
  }
  function searchBox(body, placeholder) {
    const wrap = el('label', 'pop-search');
    wrap.append(icon('search'));
    const search = el('input');
    search.type = 'search';
    search.placeholder = placeholder;
    search.setAttribute('aria-label', placeholder);
    wrap.append(search);
    body.append(wrap);
    return search;
  }
  function chooser(anchor, heading, expected, at, choose, {callsOnly = false, extra, context, previous, filter, vacate} = {}) {
    const family = expected ? familyOf(expected) : undefined;
    const body = open(anchor, heading, {cls: 'chooser', family, subtitle: expected ? 'Needs ' + (numeric(expected) ? 'a number (' + expected + ')' : expected === 'string' ? 'text' : 'a ' + expected) : undefined});
    const search = searchBox(body, callsOnly ? 'Find a block' : numeric(expected) ? 'Type a number or search' : 'Find a block or value');
    const list = options_(body);
    const typed = !callsOnly && (numeric(expected) || expected === 'string' || !expected);
    let quickBox;
    if (typed) {
      quickBox = group(list, 'Use what you typed');
      quickBox.dataset.dynamic = 'true';
      quickBox.hidden = quickBox.previousElementSibling.hidden = true;
    }
    const target = previous?.kind === 'Reference' && declarations.find(s => s.name === previous.label && s.end <= at);
    if (target || vacate) {
      const box = group(list, 'Current value');
      if (target) {
        option(box, 'Go to ' + target.name, () => { close(); focusStatement(statements.indexOf(target)); },
          {kind: 'link', family: familyOf(typeOf(previous)), hint: 'definition'});
      }
      if (target && vacate) {
        option(box, 'Move ' + target.name + ' to another input…', () => carryByKeyboard({...carried(target), node: previous, at, vacate}),
          {kind: 'link', family: familyOf(typeOf(previous)), hint: 'Tab, Enter'});
      }
      if (vacate) option(box, vacate.removes ? 'Remove this input' : 'Empty this input', () => empty(vacate), {kind: 'clear', hint: 'Del'});
    }
    if (extra) extra(list);
    if (!callsOnly) {
      const choices = enumeration(context);
      if (choices) {
        const box = group(list, 'Choose an option');
        for (const [value, meaning] of Object.entries(choices)) {
          option(box, human(value), () => choose(JSON.stringify(value)), {kind: 'enum', hint: meaning}).title = meaning;
        }
      }
      const refs = available(at, expected, context).filter(s => !filter || filter({result: bindings[s.name]?.type || known.get(s.name)}));
      if (refs.length) {
        const box = group(list, 'Your values');
        for (const s of refs) option(box, s.name, () => choose(s.name), {kind: 'ref', family: familyOf(bindings[s.name]?.type || known.get(s.name)), hint: bindings[s.name]?.type});
      }
      const fieldChoices = [];
      for (const s of declarations.filter(s => s.end <= at)) {
        for (const [key, type] of Object.entries(bindings[s.name]?.fields || {})) {
          const kinds = bindings[s.name]?.field_inputs?.[key];
          const fits = context && kinds ? kinds.includes(context.sig.input_kinds[context.param]) : accepts(type, expected, null, context);
          if (fits) fieldChoices.push([s.name + '.' + key, type]);
        }
      }
      if (fieldChoices.length) {
        const box = group(list, 'Fields of your values');
        for (const [value, type] of fieldChoices) option(box, value, () => choose(value), {kind: 'field', family: familyOf(type), hint: type});
      }
      const literals = [['integer', 'Whole number', '1'], ['exact number', 'Exact number', '1/20'], ['string', 'Text', '""'], ['list', 'Empty list', '[]']];
      const fits = numeric(expected) ? (QUICK[expected] || []).map(v => [expected, v, v]) : literals.filter(([t]) => accepts(t, expected));
      if (fits.length) {
        const box = group(list, 'Values');
        for (const [, label, value] of fits) option(box, label, () => choose(value), {kind: 'value', family: 'value'});
      }
    }
    const grouped = new Map();
    for (const sig of library) {
      if (filter ? !filter(sig) : !accepts(sig.result, expected, null, context)) continue;
      const key = sig.module || 'Operations';
      if (!grouped.has(key)) grouped.set(key, group(list, sig.module ? 'Blocks · ' + moduleTitle(sig.module) : 'Checks'));
      const item = miniBlock(sig, 'pal-block opt opt-block');
      item.setAttribute('role', 'option');
      item.addEventListener('click', () => choose(replacementCall(sig, at, previous), sig.module));
      item.title = sig.description || sig.typed_signature || sig.name;
      grouped.get(key).append(item);
    }
    if (!list.querySelector('.opt')) list.append(el('p', 'pop-empty', 'No block produces this kind of value yet.'));
    filterable(list, search, query => {
      if (!quickBox) return 0;
      quickBox.replaceChildren();
      let value;
      if (query && number.test(query) && (numeric(expected) || !expected)) value = query.replace(/\s+/g, '');
      else if (query && (expected === 'string' || (!expected && !ident.test(query)))) value = JSON.stringify(query);
      quickBox.hidden = quickBox.previousElementSibling.hidden = !value;
      if (value) option(quickBox, 'Use ' + value, () => choose(value), {kind: 'value', family: 'value', hint: 'Enter'});
      return value ? 1 : 0;
    });
    navigable(list, search);
    search.focus();
  }
  function consumers(anchor, statement) {
    const body = open(anchor, 'Use ' + statement.name + ' in…', {subtitle: 'Each choice adds a new block that takes ' + statement.name, family: familyOf(bindings[statement.name]?.type)});
    const search = searchBox(body, 'Find a block');
    const list = options_(body);
    const targets = bindings[statement.name]?.accepts || {};
    for (const [module, constructors] of Object.entries(targets)) {
      const box = group(list, module ? moduleTitle(module) : 'Checks');
      for (const [name, params] of Object.entries(constructors)) {
        const sig = library.find(s => s.name === name) || allCalls.get(name);
        if (!sig) continue;
        for (const param of params) {
          const item = option(box, human(name) + ' · ' + human(param), () =>
            addDeclaration(callValue(sig, chars.length, {[param]: statement.name}), module || undefined, near(statement)), {kind: 'block', family: familyOf(sig.result), hint: sig.result});
          item.title = sig.typed_signature;
        }
      }
    }
    if (!list.querySelector('.opt')) {
      list.append(el('p', 'pop-empty', Object.hasOwn(bindings, statement.name) ?
        'No block takes this value as an input.' : 'Fix the problems in this study first: StatClaim could not type this value.'));
    }
    filterable(list, search);
    navigable(list, search);
    search.focus();
  }

  // Blocks ------------------------------------------------------------------
  // A value's connector sits on its left edge; an empty input shows the connector it takes.
  function keyed(node, family, cls) {
    const key = keyShape(family, cls);
    if (!key) return null;
    node.prepend(key);
    node.classList.add('keyed');
    return key;
  }
  function shell(node, cls) {
    const block = el('div', 'blk ' + cls);
    block.dataset.kind = node.kind;
    block.dataset.start = node.start;
    block.dataset.end = node.end;
    return block;
  }
  function literalEditor(block, initial, {string, commit, preview, label, expected}) {
    const input = el('input', 'lit-input' + (string ? ' lit-text' : ' lit-number'));
    input.type = 'text';
    input.value = initial;
    input.spellcheck = false;
    input.setAttribute('aria-label', label);
    if (!initial) input.placeholder = string ? 'text' : 'number';
    const fit = () => { input.style.width = 'calc(' + Math.max(2, Math.min(36, Array.from(input.value || input.placeholder).length + 0.6)) + 'ch + 24px)'; };
    fit();
    const text = () => string ? JSON.stringify(input.value) : input.value.trim();
    let token = 0;
    input.addEventListener('input', () => {
      fit();
      const value = text();
      if (!string && !number.test(value)) {
        input.setAttribute('aria-invalid', 'true');
        showBubble(input, value ? NUMBER_HINT : 'Enter a value.');
        token++;
        options.onCancelPreview?.();
        return;
      }
      input.removeAttribute('aria-invalid');
      hideBubble();
      const id = ++token;
      Promise.resolve(preview?.(value)).then(result => {
        if (id !== token || document.activeElement !== input || !result) return;
        const problems = result.diagnostics || [];
        const own = problems.filter(d => d.severity === 'error');
        if (own.length) {
          input.setAttribute('aria-invalid', 'true');
          showBubble(input, codeTitle(own[0].code) + ': ' + own[0].message);
        } else showBubble(input, problems.length ? 'Valid, with ' + plural(problems.length, 'open obligation') + ': ' + problems[0].message : 'Compiles with this value', problems.length ? 'warning' : 'ok');
      }).catch(() => {});
    });
    let settled = false;
    input.addEventListener('change', () => {
      if (settled) return;
      const value = text();
      if (!string && !number.test(value)) {
        input.setAttribute('aria-invalid', 'true');
        showBubble(input, NUMBER_HINT);
        return;
      }
      if (value !== (string ? JSON.stringify(initial) : initial)) commit(value);
    });
    input.addEventListener('keydown', event => {
      if (event.key === 'Enter') input.blur();
      if (event.key === 'Escape') {
        input.value = initial;
        input.removeAttribute('aria-invalid');
        options.onCancelPreview?.();
        hideBubble();
        input.blur();
      }
    });
    input.addEventListener('blur', () => setTimeout(() => { if (document.activeElement !== input) hideBubble(); }, 1500));
    block.append(input);
    // Drag a number left or right to change it; a click without moving still types.
    if (!string && scrubber(initial, expected)) {
      input.classList.add('scrubbable');
      input.title = 'Drag left or right to change' + (expected === 'level' ? '' : ', Shift for bigger steps') + ' · click to type';
      input.addEventListener('pointerdown', down => {
        if (down.button !== 0 || document.activeElement === input || options.readOnly) return;
        const ruler = scrubber(input.value, expected);
        if (!ruler) return;
        down.preventDefault();
        const from = input.value;
        let moving = false;
        let shown = from;
        let timer = null;
        const drag = new AbortController();
        const on = (type, handler) => window.addEventListener(type, handler, {signal: drag.signal});
        const preview = () => {
          if (timer) return;
          timer = setTimeout(() => { timer = null; input.dispatchEvent(new Event('input')); }, 90);
        };
        const stop = () => {
          drag.abort();
          clearTimeout(timer);
          timer = null;
          block.classList.remove('scrubbing');
          document.body.classList.remove('scrubbing');
        };
        on('pointermove', move => {
          const dx = move.clientX - down.clientX;
          if (!moving) {
            if (Math.abs(dx) < 4) return;
            moving = true;
            block.classList.add('scrubbing');
            document.body.classList.add('scrubbing');
            input.focus({preventScroll: true});
          }
          move.preventDefault();
          const next = ruler.at(Math.trunc(dx / ruler.px), move.shiftKey);
          if (next === shown) return;
          shown = next;
          input.value = next;
          fit();
          preview();
        });
        on('pointerup', () => {
          stop();
          if (!moving) {
            // A click: type a new value.
            input.focus({preventScroll: true});
            input.select?.();
            return;
          }
          if (shown !== initial) {
            settled = true;
            options.onScrubbed?.();
            commit(shown);
          } else {
            input.blur();
            options.onCancelPreview?.();
          }
        });
        on('pointercancel', () => { stop(); input.value = from; fit(); });
        on('keydown', key => {
          if (key.key !== 'Escape') return;
          stop();
          input.value = from;
          fit();
          input.dispatchEvent(new Event('input'));
          input.blur();
          options.onCancelPreview?.();
        });
      });
    }
    // A level also reads as a percentage.
    if (!string && expected === 'level') {
      const percent = el('span', 'lit-percent');
      const show = () => {
        const value = numberOf(input.value);
        percent.textContent = value > 0 && value < 1 ? '= ' + +(value * 100).toPrecision(3) + '%' : '';
      };
      input.addEventListener('input', show);
      show();
      block.append(percent);
    }
    // A whole number steps with − and +, or with the arrow keys (Shift for tens).
    if (!string && (expected === 'integer' || (!expected && /^-?\d+$/.test(initial)))) {
      const step = delta => {
        const now = Number(input.value);
        if (!Number.isInteger(now)) return;
        input.value = String(Math.max(0, now + delta));
        fit();
      };
      input.addEventListener('keydown', event => {
        if (event.key !== 'ArrowUp' && event.key !== 'ArrowDown') return;
        event.preventDefault();
        step((event.key === 'ArrowUp' ? 1 : -1) * (event.shiftKey ? 10 : 1));
        input.dispatchEvent(new Event('input'));
      });
      const tools = el('span', 'lit-steps');
      tools.append(
        iconButton('minus', 'Decrease ' + label, () => { step(-1); commit(input.value); }, 'lit-step'),
        iconButton('plus', 'Increase ' + label, () => { step(1); commit(input.value); }, 'lit-step'));
      block.classList.add('has-steps');
      block.append(tools);
    } else if (!string && scrubber(initial, expected)) {
      // Levels and rates step from the keyboard as they do when dragged.
      input.addEventListener('keydown', event => {
        if (event.key !== 'ArrowUp' && event.key !== 'ArrowDown') return;
        const ruler = scrubber(input.value, expected);
        if (!ruler) return;
        event.preventDefault();
        input.value = ruler.at(event.key === 'ArrowUp' ? 1 : -1, event.shiftKey);
        fit();
        input.dispatchEvent(new Event('input'));
      });
    }
    return input;
  }
  const numberOf = text => {
    const [a, b] = String(text).replace(/\s+/g, '').split('/');
    return b === undefined ? Number(a) : Number(a) / Number(b);
  };
  function render(node, at, ctx = {}) {
    const children = node.children || [];
    if (node.kind === 'Literal') {
      const block = shell(node, 'blk-lit');
      const string = node.literal.startsWith('"');
      const choices = string && enumeration(ctx.context);
      // A dropdown takes its colour from the block around it, as in Scratch.
      if (!choices) setFamily(block, typeOf(node));
      if (choices) {
        const current = JSON.parse(node.literal);
        const select = el('select', 'lit-select');
        select.setAttribute('aria-label', ctx.label || 'Option');
        for (const [value, meaning] of Object.entries(choices)) {
          const item = choice(human(value), value);
          item.title = meaning;
          select.append(item);
        }
        if (!Object.hasOwn(choices, current)) select.append(choice(current, current));
        select.value = current;
        select.title = choices[current] || '';
        select.addEventListener('change', () => change(node.start, node.end, JSON.stringify(select.value)));
        block.append(select);
        block.classList.add('blk-enum');
        return block;
      }
      literalEditor(block, string ? JSON.parse(node.literal) : node.literal, {
        string, label: ctx.label || (string ? 'Text value' : 'Number'), expected: ctx.expected,
        commit: value => change(node.start, node.end, value),
        preview: value => options.onPreview?.(applyEdits(source, [stamp(node, value)])),
      });
      // A simulation's seed can be rerolled, to see how much the estimate moves.
      if (ctx.context?.param === 'seed' && !string) {
        const roll = iconButton('dice', 'Try another seed', () => change(node.start, node.end, String(1 + Math.floor(Math.random() * 99999))), 'icon-btn seed-roll');
        block.append(roll);
      }
      return block;
    }
    if (node.kind === 'Reference') {
      const block = shell(node, 'blk-ref');
      const target = declarations.find(s => s.name === node.label && s.end <= at);
      const hole = !target && node.label.startsWith('choose_');
      if (hole && ctx.replace && (numeric(ctx.expected) || ctx.expected === 'string')) {
        setFamily(block, ctx.expected);
        block.classList.add('blk-hole');
        literalEditor(block, '', {
          string: ctx.expected === 'string', label: ctx.label || 'Value',
          commit: value => ctx.replace(value),
          preview: value => options.onPreview?.(applyEdits(source, [stamp(node, value)])),
        });
        return block;
      }
      const type = hole ? ctx.expected : typeOf(node);
      setFamily(block, type);
      keyed(block, familyOf(type), hole ? 'key key-ghost' : 'key');
      const pill = button(hole ? (ctx.expected || 'Choose') : node.label, () => {
        if (ctx.pick) ctx.pick();
        else if (target) focusStatement(statements.indexOf(target));
      }, 'pill' + (hole ? ' pill-hole' : '') + (!hole && !target ? ' pill-unknown' : ''));
      pill.dataset.ref = node.label;
      pill.setAttribute('aria-label', (ctx.label ? ctx.label + ': ' : '') + (hole ? 'empty, choose ' + (ctx.expected || 'a value') : node.label));
      const takes = ctx.context?.sig?.accepted_results?.[ctx.context.param];
      pill.title = hole ? 'Choose a ' + (takes?.length > 1 ? takes.slice(0, -1).join(', ') + ' or ' + takes.at(-1) : ctx.expected || 'value') : target ? node.label + ' · ' + (type || 'value') + ' · click to change, ' + (ctx.vacate ? 'drag to move, ⌥ drag to copy' : 'drag to copy') : node.label + ' is not declared above this point';
      if (ctx.vacate) emptyKeys(pill, ctx.vacate);
      if (target) {
        pill.classList.add('grabbable');
        pill.addEventListener('pointerdown', event => press(event, {...carried(target), ...(ctx.vacate && {node, at, vacate: ctx.vacate})}, block));
        pill.addEventListener('mouseenter', () => link(node.label, true));
        pill.addEventListener('mouseleave', () => link(node.label, false));
      }
      if (ctx.pick) block.contextMenu = () => ctx.pick();
      block.append(pill);
      return block;
    }
    if (node.kind === 'FieldAccess') {
      const block = shell(node, 'blk-field');
      setFamily(block, typeOf(node));
      const subject = children[0];
      socket(block, subject, null, at, (v, m) => change(subject.start, subject.end, v, m), 'field owner');
      block.append(el('span', 'field-dot', '.'));
      const available = Object.keys(fields(subject));
      const current = node.label.slice(1);
      const fieldStart = node.end - Array.from(current).length;
      if (available.length) {
        const select = el('select', 'lit-select field-select');
        select.setAttribute('aria-label', 'Field');
        for (const key of available) select.append(choice(human(key), key));
        if (!available.includes(current)) select.append(choice(current, current));
        select.value = current;
        select.addEventListener('change', () => change(fieldStart, node.end, select.value));
        block.append(select);
      } else {
        const input = el('input', 'lit-input lit-text');
        input.value = current;
        input.setAttribute('aria-label', 'Field name');
        input.addEventListener('change', () => {
          if (ident.test(input.value)) change(fieldStart, node.end, input.value);
          else showBubble(input, 'A field name uses letters, digits and underscores.');
        });
        block.append(input);
      }
      return block;
    }
    const list = node.kind === 'ListExpr';
    const sig = !list && allCalls.get(node.label);
    const block = shell(node, list ? 'blk-list' : 'blk-call');
    blockInfo.set(block, {node, at});
    if (ctx.root) block.classList.add('blk-root');
    setFamily(block, list ? 'list' : sig?.result);
    if (!ctx.root) keyed(block, block.dataset.family);
    if (!list && !sig) block.classList.add('blk-unknown');
    const names = Object.keys(sig?.parameters || {});
    const label = list ? 'list' : human(node.label);
    const head = el('div', 'blk-head');
    const handle = button(label, () => blockMenu(handle, node, at, ctx), 'blk-name');
    handle.setAttribute('aria-label', 'Options for ' + label);
    if (sig) handle.addEventListener('mouseenter', () => options.onHelp?.(sig, true));
    handle.title = (sig?.typed_signature || label) + (ctx.root ? '' : ctx.vacate ? ' · drag to move, ⌥ drag to copy' : ' · drag to copy');
    if (!ctx.root) {
      block.contextMenu = anchor => blockMenu(anchor, node, at, ctx);
      if (ctx.vacate) emptyKeys(handle, ctx.vacate);
      handle.classList.add('grabbable');
      handle.addEventListener('pointerdown', event => press(event, {...lifted(node), at, vacate: ctx.vacate, title: label}, block));
    }
    head.append(handle);
    // Cited and declared guarantees must not look like proved ones.
    const tier = {'Cited analyses': 'cited', 'Declared analyses': 'declared'}[options.module_info?.[sig?.module]?.classification];
    if (tier) {
      const badge = el('span', 'tier tier-' + tier, tier);
      badge.title = tier === 'cited' ? 'Guarantee cited from the literature, not proved here' : 'Guarantee declared by the author: the weakest evidence';
      head.append(badge);
    }
    block.append(head);
    const params = el('div', 'params');
    const inline = list && children.every(c => ['Reference', 'Literal'].includes(c.kind)) && children.length <= 6;
    if (list) params.classList.add(inline ? 'params-inline' : 'params-stacked');
    const used = new Set();
    children.forEach((child, i) => {
      const param = child.argument || names[i];
      if (param) used.add(param);
      const text = list ? String(i + 1) : param ? human(param) : 'argument ' + (i + 1);
      const row = el('div', 'param');
      row.dataset.param = param || String(i);
      const wide = (child.kind === 'Call' && child.children?.length) || (child.kind === 'ListExpr' && child.children.some(c => c.kind === 'Call'));
      if (wide) row.classList.add('param-wide');
      row.append(el('span', 'param-label' + (list ? ' param-index' : ''), text));
      const removable = list || ((sig?.optional || []).includes(param) && !children.slice(i + 1).some(c => !c.argument));
      const slotLabel = list ? 'item ' + (i + 1) : text;
      // Taking a value out removes an optional input or list item, and leaves a required input empty.
      const vacate = isHole(child) ? null : Object.assign(() => removable ? removalEdits(node, i) : [stamp(child, holeName(param))], {removes: removable, label: slotLabel});
      socket(row, child, sig?.parameters?.[param], at, (v, m) => change(child.start, child.end, v, m), slotLabel,
        sig && {sig, param}, removable ? () => removeChild(node, i) : null, vacate);
      if (list && i > 0) {
        const previous = children[i - 1];
        row.append(iconButton('up', 'Move item ' + (i + 1) + ' earlier', () => edit([
          stamp(previous, slice(child.start, child.end)), stamp(child, slice(previous.start, previous.end)),
        ]), 'icon-btn param-tool'));
      }
      if (removable) row.append(iconButton('x', 'Remove ' + slotLabel, () => removeChild(node, i), 'icon-btn param-tool param-remove'));
      params.append(row);
    });
    if (list) {
      const add = button('', () => chooser(add, 'Add a list item', null, at, (v, m) => appendChild(node, v, m)), 'param-add');
      add.append(icon('plus'), 'item');
      add.setAttribute('aria-label', 'Add item');
      params.append(add);
    } else {
      for (const name of names.filter(n => !used.has(n))) {
        const required = !(sig.optional || []).includes(name);
        const add = button('', () => chooser(add, 'Add ' + human(name), sig.parameters[name], at,
          (v, m) => appendChild(node, name + '=' + v, m), {context: {sig, param: name}}), 'param-add' + (required ? ' required' : ''));
        add.append(icon('plus'), human(name));
        const glyph = keyGlyph(familyOf(sig.parameters[name]));
        if (glyph) add.append(glyph);
        add.setAttribute('aria-label', 'Add ' + human(name));
        add.title = (required ? 'Required input · ' : 'Optional input · ') + sig.parameters[name];
        params.append(add);
      }
    }
    if (params.children.length) block.append(params);
    return block;
  }
  function socket(parent, node, expected, at, replace, label, context, remove, vacate) {
    const slot = el('div', 'slot');
    slot.dataset.slot = label;
    if (expected) {
      slot.dataset.accepts = expected;
      slot.dataset.expect = familyOf(expected);
    }
    const pick = () => chooser(slot, 'Choose ' + label, expected, at, replace, {context, previous: node, vacate});
    slot.append(render(node, at, {expected, label, context, pick, replace, remove, vacate}));
    if (node.kind === 'Literal' || slot.querySelector(':scope > .blk-hole')) {
      slot.append(iconButton('chevron', 'Choose ' + label, pick, 'icon-btn slot-pick'));
    }
    sockets.push({slot, expected, at, replace, context, node, pick});
    parent.append(slot);
    return slot;
  }
  // An analysis whose contract does not cover the declared null can switch to one that does.
  // Changing the null is never offered: it would change the statistical question.
  function nullPredicate(node, at) {
    const sig = allCalls.get(node.label);
    if (!sig?.parameters?.null) return null;
    const names = Object.keys(sig.parameters);
    let child = node.children.find((c, i) => (c.argument || names[i]) === 'null');
    for (let guard = 0; child?.kind === 'Reference' && guard < 50; guard++) {
      const name = child.label;
      child = declarations.find(d => d.name === name && d.end <= at)?.expression;
    }
    return child?.kind === 'Call' ? child.label : null;
  }
  function mismatch(node, at) {
    const sig = node.kind === 'Call' && allCalls.get(node.label);
    const supported = sig?.contract?.supported_predicates;
    const predicate = supported && nullPredicate(node, at);
    if (!predicate || supported.includes(predicate)) return null;
    return {sig, predicate, alternatives: library.filter(other => other.contract?.supported_predicates?.includes(predicate))};
  }
  function switchAnalysis(node, target, extra = {}) {
    const names = Object.keys(allCalls.get(node.label)?.parameters || {});
    const supplied = {...extra};
    node.children.forEach((child, i) => {
      const param = child.argument || names[i];
      if (param && target.parameters[param] && !Object.hasOwn(supplied, param)) supplied[param] = slice(child.start, child.end);
    });
    change(node.start, node.end, callValue(target, node.start, supplied), target.module);
    options.onToast?.('Switched to ' + human(target.name) + '; your null is unchanged', {undo: true});
  }
  const TIER = {'Cited analyses': 'cited', 'Declared analyses': 'declared'};
  function fixesAt(element) {
    for (let node = element?.closest?.('.blk-call'); node && host.contains(node); node = node.parentElement?.closest('.blk-call')) {
      const info = blockInfo.get(node);
      const found = info && mismatch(info.node, info.at);
      if (!found) continue;
      const nullSig = allCalls.get(found.predicate);
      const fixes = found.alternatives.map(target => ({
        label: 'Use ' + human(target.name), note: target.contract?.expected_null, family: familyOf(target.result),
        tier: TIER[options.module_info?.[target.module]?.classification], apply: () => switchAnalysis(info.node, target),
      }));
      const declared = allCalls.get('declared_test');
      if (!fixes.length && declared) {
        fixes.push({label: 'Declare your own test', note: 'You name the test and vouch for it. This is the weakest evidence.', tier: 'declared',
          family: familyOf(declared.result), apply: () => switchAnalysis(info.node, declared, {method: '"name of your test"'})});
      }
      return {
        summary: human(found.sig.name) + ' supports ' + found.sig.contract.supported_predicates.map(human).join(' or ') +
          ', not ' + human(found.predicate) + (nullSig?.description ? '' : '.'),
        empty: found.alternatives.length ? '' : 'No registered analysis supports a ' + human(found.predicate) + ' null.',
        fixes,
      };
    }
    return null;
  }
  const fixList = (parent, found, done) => parent.append(fixBox(found, done));
  function blockMenu(anchor, node, at, ctx) {
    const list = node.kind === 'ListExpr';
    const sig = !list && allCalls.get(node.label);
    const label = list ? 'List' : human(node.label);
    const body = open(anchor, label, {cls: 'menu', family: familyOf(list ? 'list' : sig?.result),
      subtitle: sig ? 'Makes ' + (sig.result ? 'a ' + sig.result : 'a value') + (sig.module ? ' · ' + sig.module : '') : list ? 'A list of values' : 'Unknown block'});
    if (sig?.description) {
      const text = sig.description.length > 220 ? sig.description.slice(0, 217).trimEnd() + '…' : sig.description;
      body.append(el('p', 'pop-text', text));
    }
    const menu = el('div', 'menu-items');
    body.append(menu);
    const found = node.kind === 'Call' && mismatch(node, at) && fixesAt(anchor.closest?.('.blk-call') || null);
    if (found) fixList(body, found, close);
    if (ctx.pick) menuItem(menu, ctx.root ? 'Replace with another block' : 'Replace with…', 'restore', ctx.pick);
    if (!ctx.root) menuItem(menu, 'Make it a shared value', 'link', () => extractDeclaration(node, at), {note: 'let …'});
    if (ctx.vacate) menuItem(menu, 'Move to another input…', 'grip', () => carryByKeyboard({...lifted(node), at, vacate: ctx.vacate, title: label}), {note: 'Tab, Enter'});
    if (ctx.vacate) menuItem(menu, ctx.vacate.removes ? 'Remove this input' : 'Empty this input', 'trash', () => empty(ctx.vacate), {danger: true, note: 'Del'});
    if (sig) menuItem(menu, 'Show help', 'book', () => { close(); options.onHelp?.(sig); });
    menu.querySelector('button')?.focus();
  }

  // Stacks -------------------------------------------------------------------
  function link(name, on) {
    host.querySelector('.stack[data-name="' + esc(name) + '"]')?.classList.toggle('linked', on);
  }
  function linkUses(name, on) {
    for (const pill of host.querySelectorAll('.pill[data-ref="' + esc(name) + '"]')) pill.classList.toggle('linked', on);
  }
  function startRename(s, pill) {
    const input = el('input', 'rename-input');
    input.value = s.name;
    input.spellcheck = false;
    input.setAttribute('aria-label', 'New name for ' + s.name);
    input.style.width = 'calc(' + Math.max(3, s.name.length + 1) + 'ch + 26px)';
    pill.replaceWith(input);
    input.focus();
    input.select();
    let done = false;
    const problem = name => !ident.test(name) ? 'Start with a letter or _, then use letters, digits or _.' :
      declarations.some(d => d.name === name && d !== s) || Object.hasOwn(operations, name) ? name + ' is already used. Choose a unique name.' : '';
    input.addEventListener('input', () => {
      input.style.width = 'calc(' + Math.max(3, input.value.length + 1) + 'ch + 26px)';
      const message = problem(input.value);
      if (message) input.setAttribute('aria-invalid', 'true'); else input.removeAttribute('aria-invalid');
      if (message) showBubble(input, message); else hideBubble();
    });
    const finish = commit => {
      if (done) return;
      const name = input.value;
      if (!commit || name === s.name || problem(name)) {
        done = true;
        hideBubble();
        input.replaceWith(pill);
        if (commit && problem(name)) options.onToast?.('Kept the name ' + s.name + ': ' + problem(name));
        return;
      }
      done = true;
      rename(s, name);
    };
    input.addEventListener('keydown', event => {
      if (event.key === 'Enter') { event.preventDefault(); if (!problem(input.value)) finish(true); }
      if (event.key === 'Escape') { event.preventDefault(); finish(false); pill.focus(); }
    });
    input.addEventListener('blur', () => finish(true));
  }
  function rename(s, name) {
    const prefix = slice(s.start, s.expression.start);
    const match = prefix.match(/^let\s+([A-Za-z_][A-Za-z_0-9]*)/);
    if (!match) return;
    const end = s.start + Array.from(match[0]).length;
    const patches = [{start: end - s.name.length, end, text: name}];
    for (const later of statements.filter(d => d.start >= s.end)) {
      walk(later.expression, n => { if (n.kind === 'Reference' && n.label === s.name) patches.push(stamp(n, name)); });
    }
    if (layout?.[s.name]) {
      const map = {...layout, [name]: layout[s.name]};
      delete map[s.name];
      saveLayout(map);
    }
    edit(patches);
    options.onToast?.('Renamed ' + s.name + ' to ' + name + (patches.length > 1 ? ' in ' + plural(patches.length - 1, 'place') : ''));
  }
  function remove(s) {
    const range = noteRange(s);
    let end = s.end;
    if (chars[end] === '\r') end++;
    if (chars[end] === '\n') end++;
    change(range.text ? range.start : s.start, end, '');
    options.onToast?.('Deleted ' + (s.name || 'the check'), {undo: true});
  }
  function duplicate(s) {
    const name = freshName(s.name);
    const text = 'let ' + name + ' = ' + slice(s.expression.start, s.expression.end);
    const after = chars[s.end] === '\n' ? s.end + 1 : s.end;
    const point = near(s);
    if (point) placeNew(name, point);
    change(after, after, (after === s.end ? '\n' : '') + text + (after === s.end ? '' : '\n'));
    options.onToast?.('Duplicated ' + s.name + ' as ' + name, {undo: true});
  }
  // Two neighbours can swap only if the later one does not use the earlier one.
  function neighbour(s, direction) {
    const j = statements.indexOf(s) + direction;
    if (j < 0 || j >= statements.length) return null;
    const [first, second] = direction < 0 ? [statements[j], s] : [s, statements[j]];
    let depends = false;
    if (first.name) walk(second.expression, n => { if (n.kind === 'Reference' && n.label === first.name) depends = true; });
    return depends ? null : {first, second, other: statements[j]};
  }
  function move(s, direction) {
    const pair = neighbour(s, direction);
    if (!pair) return;
    const a = {start: noteRange(pair.first).start, end: pair.first.end};
    const b = {start: noteRange(pair.second).start, end: pair.second.end};
    const toA = {...a, text: slice(b.start, b.end)};
    const toB = {...b, text: slice(a.start, a.end)};
    edit(direction < 0 ? [toA, toB] : [toB, toA]);
  }
  function stackMenu(anchor, s, card) {
    const type = bindings[s.name]?.type || typeOf(s.expression);
    const body = open(anchor, s.name || 'Check', {cls: 'menu', family: familyOf(type), subtitle: type || undefined});
    const menu = el('div', 'menu-items');
    body.append(menu);
    if (s.name) {
      menuItem(menu, 'Use in another block…', 'link', () => consumers(anchor, s));
      menuItem(menu, 'Rename', 'pencil', () => { close(); startRename(s, card.querySelector('.stack-name')); });
    }
    if (card.pickRoot) menuItem(menu, 'Replace with another block', 'restore', card.pickRoot);
    if (s.name && options.onExplain && ['analysis', 'family'].includes(familyOf(bindings[s.name]?.type))) {
      menuItem(menu, 'Why does it fit?', 'info', () => whyPopover(anchor, s.name), {note: 'contract'});
    }
    const rootSig = s.expression.kind === 'Call' && allCalls.get(s.expression.label);
    if (rootSig) menuItem(menu, 'Show help', 'book', () => { close(); options.onHelp?.(rootSig); });
    const note = noteRange(s);
    menuItem(menu, note.text ? 'Edit note' : 'Add note', 'note', () => editNote(anchor, note, 'Note for ' + (s.name || 'this check')));
    if (s.name) menuItem(menu, 'Duplicate', 'copy', () => duplicate(s));
    const up = neighbour(s, -1);
    const down = neighbour(s, 1);
    const index = statements.indexOf(s);
    if (index > 0) menuItem(menu, 'Move earlier in file', 'up', () => move(s, -1), {disabled: !up, note: up ? undefined : 'uses ' + statements[index - 1].name});
    if (index < statements.length - 1) menuItem(menu, 'Move later in file', 'down', () => move(s, 1), {disabled: !down, note: down ? undefined : 'used by ' + (statements[index + 1].name || 'the next check')});
    if (s.name) menuItem(menu, folded.has(s.name) ? 'Expand' : 'Collapse', 'fold', () => { close(); toggleFold(s, card); });
    const consumers_ = [...(users.get(s.name) || [])].map(i => statements[i].name || 'a check');
    menuItem(menu, 'Delete', 'trash', () => remove(s), {danger: true, disabled: s.name && consumers_.length,
      note: s.name && consumers_.length ? 'used by ' + consumers_.join(', ') : undefined});
    menu.querySelector('button:not(:disabled)')?.focus();
  }
  function toggleFold(s, card) {
    if (folded.has(s.name)) folded.delete(s.name); else folded.add(s.name);
    paintFold(s, card);
    glide();
  }
  function paintFold(s, card) {
    const collapsed = folded.has(s.name);
    card.classList.toggle('folded', collapsed);
    card.querySelector('.stack-body').hidden = collapsed;
    const fold = card.querySelector('.hat-fold');
    fold.setAttribute('aria-expanded', String(!collapsed));
    fold.setAttribute('aria-label', (collapsed ? 'Expand ' : 'Collapse ') + s.name);
    fold.title = collapsed ? 'Expand' : 'Collapse';
  }
  // A check block shows its last run under it: the grade, or a button to run it.
  const isCheck = s => {
    let found = false;
    walk(s.expression, n => { if (n.kind === 'Call' && Object.hasOwn(operations, n.label)) found = true; });
    return found;
  };
  // A check whose operation builds a proof, such as verify(...), which needs Lean.
  const usesLean = s => {
    let found = false;
    walk(s.expression, n => { if (n.kind === 'Call' && (options.leanOperations || []).includes(n.label)) found = true; });
    return found;
  };
  const statementAt = span => {
    const position = offset(span.line, span.column);
    return statements.find(s => s.start <= position && position <= s.end);
  };
  function runValue(name) {
    const run = options.results;
    if (!run || run.running || !run.values || !Object.hasOwn(run.values, name)) return null;
    return valueText(run.values[name]);
  }
  // A check Lean certified wears a medal. Only a full proof earns it: a combination with
  // assumed members, a citation or a calculation does not. It fades when the study changes.
  function certification(s) {
    const run = options.results;
    if (!run || run.running) return null;
    const request = (run.requests || []).find(found => statementAt(found.source) === s && found.status === 'verified' && !outcome(found).weakest);
    if (!request) return null;
    const old = run.stale || request.outdated;
    const stamp = button('', () => options.onShowResult?.(request.request_id), 'cert-stamp');
    stamp.append(certStamp());
    stamp.title = old ? 'Certified in Lean before your last edit. Run again to certify this version.' : 'Certified in Lean: a checked proof of the guarantee. Click for the result.';
    stamp.setAttribute('aria-label', old ? 'Certified in Lean before your last edit' : 'Certified in Lean. Show the result');
    if (old) stamp.dataset.stale = 'true';
    const key = (s.name || s.start) + '|' + (request.certificate || request.request_id);
    if (!old && !stampedChecks.has(key)) stamp.classList.add('landing');
    stampedChecks.add(key);
    return stamp;
  }
  function tray(s) {
    if (!isCheck(s)) return null;
    const run = options.results;
    const box = el('div', 'result-tray');
    if (run?.running) {
      box.dataset.state = 'running';
      box.append(el('span', 'run-spinner'), el('span', 'tray-text', options.lean === false ? 'Checking with StatClaim…' : 'Checking with StatClaim and Lean…'), el('span', 'run-bar'));
      return box;
    }
    const mine = (run?.requests || []).filter(request => statementAt(request.source) === s);
    if (mine.length) {
      box.dataset.state = 'done';
      if (run.stale) box.dataset.stale = 'true';
      // Two rows: the grade with its links, then what the run found in full width.
      for (const request of mine) {
        const info = outcome(request);
        const line = el('div', 'result-line');
        line.dataset.tone = info.tone;
        const old = run.stale || request.outdated;
        if (old) line.dataset.stale = 'true';
        const top = el('div', 'result-top');
        top.append(outcomeBadge(request, 'outcome', true));
        const links = el('span', 'tray-links');
        if (old) links.append(el('span', 'tray-stale', 'outdated'));
        else if (run.recalculating && request.operation === 'calculate') links.append(el('span', 'run-spinner small'));
        const more = button('Details', () => options.onShowResult?.(request.request_id), 'tray-link');
        more.setAttribute('aria-label', info.label + (info.scope ? ', ' + info.scope : '') + (old ? ', outdated' : '') + '. Show details');
        links.append(more);
        if (request.status === 'needs_lean' && options.onNeedsLean) links.append(button('Get a proof', () => options.onNeedsLean(), 'tray-link lean-link'));
        if (request.subject && options.onExplain) {
          const why = button('Why?', () => whyPopover(why, request.subject), 'tray-link why-btn');
          why.title = 'Why ' + request.subject + ' fits its contract';
          links.append(why);
        }
        top.append(links);
        line.append(top);
        const found = headline(request);
        if (found) {
          const text = el('p', 'tray-headline', found.text);
          if (found.tone) text.dataset.tone = found.tone;
          if (found.title) text.title = found.title;
          line.append(text);
        }
        if (info.scope) line.append(el('p', 'tray-scope', info.scope.replace(/^./, ch => ch.toUpperCase())));
        if (info.weakest) line.append(el('p', 'tray-weak', 'Only as strong as its weakest part: ' + info.weakest.grade + ' (' + info.weakest.parts.join(', ') + ')'));
        box.append(line);
      }
      return box;
    }
    box.dataset.state = 'idle';
    const go = button('', () => options.onRun?.(), 'run-btn');
    go.append(icon('play'), run?.error ? 'Run again' : 'Run check');
    go.disabled = !options.canRun;
    go.title = options.canRun ? 'Run every check in this study' : 'Fix the errors in this study before running it';
    const proof = options.lean === false && usesLean(s);
    box.append(go, el('span', 'tray-text', run?.error ? run.error : !options.canRun ? 'Fix the errors first.' :
      proof ? 'Its proof needs Lean, which this studio cannot run.' : options.lean === false ? 'Reports how strong its evidence is.' : 'Proves it in Lean, or reports how strong its evidence is.'));
    if (proof && !run?.error && options.onNeedsLean) box.append(button('Get a proof', () => options.onNeedsLean(), 'tray-link lean-link'));
    return box;
  }
  function drawStack(s, index) {
    const card = el('article', 'stack');
    card.dataset.start = s.start;
    card.dataset.end = s.end;
    if (s.name) card.dataset.name = s.name;
    card.tabIndex = 0;
    card.setAttribute('aria-label', (s.name ? s.name + ', ' : 'Check, ') + human(s.expression.label || s.expression.kind) +
      '. Arrow keys move between blocks; Option and arrows move this block; Enter for its menu.');
    card.style.setProperty('--i', Math.min(index, 14));
    const type = s.name ? bindings[s.name]?.type || typeOf(s.expression) : typeOf(s.expression);
    setFamily(card, type || (s.name ? undefined : 'VerificationResult'));
    const note = noteRange(s);
    if (note.text) {
      const aside = button('', () => editNote(aside, note, 'Note for ' + (s.name || 'this check')), 'stack-note');
      aside.append(icon('note'), el('span', 'stack-note-text', prose(note.text)));
      aside.title = 'Edit note';
      card.append(aside);
    }
    const hat = el('header', 'hat');
    if (s.name) {
      const name = button(s.name, () => startRename(s, name), 'stack-name');
      keyed(name, familyOf(type));
      name.classList.add('grabbable');
      name.setAttribute('aria-label', s.name + ', rename');
      name.title = 'Click to rename · drag into an input to use ' + s.name;
      name.addEventListener('pointerdown', event => press(event, {...carried(s), avatar: () => pillAvatar(s.name, familyOf(type))}, name));
      name.addEventListener('mouseenter', () => linkUses(s.name, true));
      name.addEventListener('mouseleave', () => linkUses(s.name, false));
      hat.append(el('span', 'hat-kw', 'let'), name, el('span', 'hat-type', type || 'value'));
    } else {
      hat.append(icon('play', 'icon hat-icon'), el('span', 'hat-kw hat-run', 'run'));
    }
    // A collapsed stack shows what it says in words, when Python can read it.
    const reading = s.name && bindings[s.name]?.reading;
    const summary = el('span', 'hat-summary', reading || (s.expression.kind === 'Call' ? human(s.expression.label) + '(…)' : ''));
    if (reading) summary.title = reading;
    // A value the last run filled in shows on its block; a collapsed stack shows it in the hat.
    const realized = s.name ? runValue(s.name) : null;
    const valueOld = realized && (options.results.stale || options.results.outdated?.includes(s.name));
    const valueTitle = realized && ((realized.title ? realized.title + '. ' : '') + (valueOld ? 'From the last run; the study has changed since.' : 'From the last run.'));
    const chip = realized && el('span', 'hat-value', '= ' + realized.text);
    if (chip) {
      chip.title = valueTitle;
      if (valueOld) chip.dataset.stale = 'true';
    }
    const issues = el('span', 'hat-issues');
    issues.hidden = true;
    const more = iconButton('more', 'More actions for ' + (s.name || 'this check'), () => stackMenu(more, s, card), 'icon-btn hat-btn');
    hat.append(summary, ...(chip ? [chip] : []), issues, el('span', 'hat-spacer'), more);
    if (s.name) hat.append(iconButton('chevron', 'Collapse ' + s.name, () => toggleFold(s, card), 'icon-btn hat-btn hat-fold'));
    card.append(hat);
    const body = el('div', 'stack-body');
    const root = el('div', 'slot slot-root');
    root.dataset.slot = s.name || 'operation';
    const expression = s.expression;
    const replaceRoot = (v, m) => change(expression.start, expression.end, v, m);
    // Offer blocks of the same kind, so a replacement keeps its uses valid.
    const rootFamily = expression.kind === 'Call' && allCalls.get(expression.label)?.result ? familyOf(allCalls.get(expression.label).result) : null;
    const pick = () => chooser(root.querySelector('.blk-name') || root, s.name ? 'Replace the value of ' + s.name : 'Replace this check', null, s.start, replaceRoot, {
      callsOnly: !s.name, previous: expression, filter: rootFamily && (sig => familyOf(sig.result) === rootFamily), extra(list) {
        const keys = Object.keys(bindings[s.name]?.fields || fields(expression));
        if (s.name && keys.length && expression.kind !== 'FieldAccess') {
          const box = group(list, 'Read a field of this value');
          for (const key of keys) option(box, '.' + key, () => change(expression.end, expression.end, '.' + key), {kind: 'field'});
        }
      }});
    card.pickRoot = pick;
    card.contextMenu = anchor => stackMenu(anchor, s, card);
    root.append(render(expression, s.start, {root: true, pick, label: s.name || 'check'}));
    if (s.name) sockets.push({slot: root, root: true, expected: null, at: s.start, replace: replaceRoot, node: expression});
    body.append(root);
    if (realized) {
      const bubble = el('output', 'value-bubble');
      bubble.append(el('span', 'value-eq', '='), el('span', 'value-text', realized.text));
      bubble.title = valueTitle;
      bubble.setAttribute('aria-label', s.name + ' is ' + realized.text + (valueOld ? ', from the last run before your edits' : ', from the last run'));
      if (valueOld) bubble.dataset.stale = 'true';
      if (shownValues.get(s.name) !== realized.text) bubble.classList.add('fresh');
      shownValues.set(s.name, realized.text);
      body.classList.add('has-value');
      body.append(bubble);
    }
    card.append(body);
    if (reading) {
      const caption = el('p', 'stack-reading', reading);
      caption.title = 'What this value says, in words';
      card.append(caption);
    }
    const results = tray(s);
    if (results) card.append(results);
    const stamp = certification(s);
    if (stamp) {
      card.classList.add('certified');
      card.append(stamp);
    }
    const consumers_ = [...(users.get(s.name) || [])];
    if (s.name && consumers_.length) {
      const foot = el('footer', 'stack-uses');
      foot.append(el('span', 'uses-label', 'used by'));
      for (const i of consumers_) {
        const other = statements[i];
        const chip = button(other.name || 'check', () => focusStatement(i), 'use-chip');
        setFamily(chip, other.name ? bindings[other.name]?.type : 'VerificationResult');
        foot.append(chip);
      }
      card.append(foot);
    } else if (s.name && !['run', 'claim'].includes(familyOf(type)) && Object.keys(bindings[s.name]?.accepts || {}).length) {
      const foot = el('footer', 'stack-uses stack-unused');
      const go = button('', () => consumers(go, s), 'use-next');
      go.append(icon('plus'), 'Use ' + s.name + ' in…');
      foot.append(el('span', 'uses-label', 'not used yet'), go);
      card.append(foot);
    }
    if (s.name) paintFold(s, card);
    const entry = {s, card, x: 0, y: 0, w: 0, h: 0};
    if (s.name && s.name === selected) card.classList.add('selected');
    card.addEventListener('pointerdown', event => { if (event.button === 0) select(entry); });
    card.addEventListener('focus', () => select(entry));
    card.addEventListener('pointerdown', event => startMove(event, entry));
    card.addEventListener('keydown', event => stackKeys(event, entry));
    card.addEventListener('mouseenter', () => { hoverCard = card; drawWires(); });
    card.addEventListener('mouseleave', () => { if (hoverCard === card) { hoverCard = null; drawWires(); } });
    stacks.push(entry);
    return card;
  }

  // Selecting ---------------------------------------------------------------------
  function select(entry) {
    const name = entry?.s.name || null;
    if (name === selected) return;
    selected = name;
    selectedFits = null;
    for (const x of stacks) {
      const on = Boolean(name) && x.s.name === name;
      x.card.classList.toggle('selected', on);
      x.card.classList.toggle('just-selected', on);
    }
    paintFits();
    options.onSelect?.(name);
  }
  // A block's entry in the fits, from its own module or another that shares it.
  const fitOf = (fits, sig) => fits?.[sig?.module || '']?.[sig?.name] ||
    Object.values(fits || {}).map(blocks => blocks[sig?.name]).find(Boolean);
  // An open input after the selected value that takes it directly is marked.
  function paintFits() {
    const declared = declarations.find(s => s.name === selected);
    for (const t of sockets) {
      const fit = declared && selectedFits && !t.root && isHole(t.node) && declared.end <= t.at && fitOf(selectedFits, t.context?.sig);
      if (fit && !fit.via && fit.inputs.includes(t.context.param)) {
        t.slot.dataset.fit = '';
        t.slot.title = 'Takes ' + selected;
      } else if (t.slot.hasAttribute('data-fit')) {
        delete t.slot.dataset.fit;
        t.slot.removeAttribute('title');
      }
    }
  }

  // Arming, dragging and placing ------------------------------------------------
  function target(slot) { return sockets.find(t => t.slot === slot); }
  function activate(test) {
    let count = 0;
    for (const t of sockets) {
      if (t.root || !test(t)) continue;
      t.slot.dataset.active = 'true';
      count++;
    }
    host.classList.toggle('placing', true);
    return count;
  }
  function clearDrag() {
    document.documentElement.classList.remove('carrying');
    dragging?.element?.classList.remove('drag-source');
    dragging = null;
    keyTarget = -1;
    hover(null);
    refuse(null);
    hint?.remove();
    hint = null;
    host.classList.remove('drop-canvas');
    options.trash?.classList.remove('trash-over');
    if (!armed) {
      host.classList.remove('placing');
      for (const {slot} of sockets) { delete slot.dataset.active; delete slot.dataset.over; }
    }
    for (const {slot} of sockets) delete slot.dataset.over;
  }
  // What a drag carries. A stack's name is always copied; a value taken from an input moves, or is copied with ⌥.
  const carried = declaration => ({declaration, text: declaration.name, title: declaration.name,
    family: familyOf(bindings[declaration.name]?.type || known.get(declaration.name))});
  const lifted = node => ({node, text: slice(node.start, node.end), loose: true, family: familyOf(typeOf(node))});
  function targetsFor(from) {
    if (from.sig) return t => accepts(from.sig.result, t.expected, null, t.context);
    if (from.declaration) return t => t.node !== from.node && available(t.at, t.expected, t.context).includes(from.declaration);
    const node = from.node;
    const dependencies = new Set();
    walk(node, child => { if (child.kind === 'Reference') dependencies.add(child.label); });
    return t => {
      const inner = t.slot.querySelector(':scope > .blk');
      if (inner && +inner.dataset.start >= node.start && +inner.dataset.end <= node.end) return false;
      const inScope = [...dependencies].every(name => declarations.some(d => d.name === name && d.end <= t.at));
      return inScope && accepts(typeOf(node), t.expected, null, t.context);
    };
  }
  function pillAvatar(label, family) {
    const block = el('div', 'blk blk-ref');
    block.dataset.family = family;
    block.append(el('span', 'pill', label));
    keyed(block, family);
    return block;
  }

  // Dragging. What is dragged follows the pointer as a solid block, with mouse, pen or touch, and snaps
  // to the inputs that take it. Pressing without moving stays a click.
  let pending = null;
  function press(event, from, element) {
    if (event.button !== 0 || dragging || armed) return;
    pending = {from, element, x: event.clientX, y: event.clientY, id: event.pointerId};
  }
  function begin(event) {
    const {from, element, x, y} = pending;
    pending = null;
    close();
    hideBubble();
    const box = element.getBoundingClientRect();
    const canvasBlock = host.contains(element) && !from.avatar;
    const face = from.avatar ? from.avatar() : element.cloneNode(true);
    face.classList.remove('drag-source', 'has-issue', 'issue-error', 'issue-warning', 'flash');
    face.querySelectorAll('.issue-badge, .param-tool, .slot-pick, .snap-ghost').forEach(n => n.remove());
    if (canvasBlock) face.style.zoom = String(zoomOf());
    const avatar = el('div', 'drag-avatar');
    avatar.setAttribute('aria-hidden', 'true');
    avatar.append(face);
    document.body.append(avatar);
    document.documentElement.classList.add('carrying');
    dragging = {...from, element, avatar, origin: {x: box.left, y: box.top},
      dx: from.avatar ? 14 : x - box.left, dy: from.avatar ? 13 : y - box.top, height: box.height || 26};
    if (from.sig) {
      armed = from.sig;
      options.onArm?.(armed);
    }
    activate(targetsFor(dragging));
    if (!from.sig) startHint(Boolean(from.loose));
    follow(event);
  }
  function follow(event) {
    const d = dragging;
    const x = event.clientX - d.dx;
    const y = event.clientY - d.dy;
    d.avatar.style.transform = 'translate(' + x + 'px, ' + y + 'px)';
    d.copy = !d.vacate || Boolean(event.altKey);
    d.avatar.classList.toggle('copying', Boolean(d.vacate && event.altKey));
    d.element.classList.toggle('drag-source', Boolean(d.vacate && !d.copy));
    const under = document.elementFromPoint?.(event.clientX, event.clientY) || null;
    d.overTrash = Boolean(d.vacate && options.trash?.contains(under));
    options.trash?.classList.toggle('trash-over', d.overTrash);
    // The block's own connector, at its left edge, is what snaps.
    const slot = d.overTrash ? null : activeSlot(under) || nearestSlot(x, y + Math.min(14, d.height / 2)) || nearestSlot(event.clientX, event.clientY);
    hover(slot);
    const nope = !slot && under?.closest?.('.slot');
    refuse(nope && nope.dataset.accepts && !nope.dataset.active && dragFamily() &&
      nope.querySelector(':scope > .blk-ref, :scope > .blk-lit, :scope > .blk-hole') ? nope : null);
    d.canvas = !slot && !d.overTrash && (d.loose || d.sig) && emptyCanvas(under) ? {x, y} : null;
    host.classList.toggle('drop-canvas', Boolean(d.canvas));
    const view = host.getBoundingClientRect();
    if (view.height) {
      if (event.clientY > view.bottom - 36) host.scrollTop += 14;
      else if (event.clientY < view.top + 36 && event.clientY > view.top) host.scrollTop -= 14;
    }
  }
  function drop(event) {
    follow(event);
    const d = dragging;
    const t = overSlot && target(overSlot);
    movedAt = Date.now();
    if (!t && !d.overTrash && !d.canvas) return cancel();
    d.avatar.remove();
    clearDrag();
    if (d.sig) {
      disarm();
      options.onArm?.(null);
    }
    if (t) d.sig ? placeArmed(t, null, d.sig) : moveInto(t, d, d.copy);
    else if (d.overTrash) empty(d.vacate);
    else d.sig ? placeArmed(undefined, boardPoint(d.canvas.x, d.canvas.y), d.sig) : moveOut(d, boardPoint(d.canvas.x, d.canvas.y), d.copy);
  }
  // Dropped where nothing takes it, the block flies back to where it came from.
  function cancel() {
    const d = dragging;
    if (!d) return;
    const avatar = d.avatar;
    clearDrag();
    if (d.sig) {
      disarm();
      options.onArm?.(null);
    }
    if (!avatar) return;
    avatar.classList.add('flying');
    avatar.style.transform = 'translate(' + d.origin.x + 'px, ' + d.origin.y + 'px)';
    setTimeout(() => avatar.remove(), 260);
  }
  listen(document, 'pointermove', event => {
    if (pending && event.pointerId === pending.id && !dragging) {
      if (Math.hypot(event.clientX - pending.x, event.clientY - pending.y) < 5) return;
      begin(event);
    }
    if (dragging?.avatar) follow(event);
  });
  listen(document, 'pointerup', event => {
    pending = null;
    if (dragging?.avatar) drop(event);
  });
  listen(document, 'pointercancel', () => {
    pending = null;
    if (dragging?.avatar) cancel();
  });
  // Keyboard: while a block is picked or a value is carried, Tab walks the inputs that take it and Enter puts it there.
  let keyTarget = -1;
  function carryByKeyboard(from) {
    close();
    dragging = {...from, keyboard: true};
    activate(targetsFor(dragging));
    keyTarget = -1;
    startHint(false);
  }
  listen(document, 'keydown', event => {
    if (dragging?.avatar && event.key === 'Escape') { event.preventDefault(); cancel(); return; }
    const carrying = dragging?.keyboard;
    if (!(armed || carrying) || dragging?.avatar || pop) return;
    if (event.key === 'Escape' && carrying) { event.preventDefault(); clearDrag(); return; }
    if (event.key === 'Tab') {
      const list = sockets.filter(t => t.slot.dataset.active);
      if (!list.length) return;
      event.preventDefault();
      keyTarget = (keyTarget + (event.shiftKey ? -1 : 1) + list.length) % list.length;
      hover(list[keyTarget].slot);
      scrollInside(host, list[keyTarget].slot, 'center');
    } else if (event.key === 'Enter' && overSlot) {
      event.preventDefault();
      event.stopPropagation();
      const t = target(overSlot);
      if (carrying) {
        const d = dragging;
        clearDrag();
        moveInto(t, d, !d.vacate || event.altKey);
      } else placeArmed(t);
    }
  }, {capture: true});
  function startHint(canvas) {
    hint?.remove();
    hint = el('div', 'place-banner drag-hint');
    hint.setAttribute('role', 'status');
    if (dragging.keyboard) {
      hint.append(el('span', 'place-text', 'Press Tab to choose an input that takes ' + dragging.title + ', Enter to ' + (dragging.vacate ? 'move' : 'put') + ' it there, or Escape to cancel.'));
    } else {
      const where = [dragging.vacate ? 'a glowing input to move it there' : 'a glowing input to copy it there'];
      if (canvas) where.push('empty canvas to make it a value of its own');
      if (dragging.vacate) where.push('the palette to remove it');
      hint.append(el('span', 'place-text', 'Drop on ' + where.join(', on ') + '.' + (dragging.vacate ? ' Hold ⌥ to copy instead.' : '')));
    }
    (options.overlay || host).prepend(hint);
  }
  function emptyKeys(control, vacate) {
    control.addEventListener('keydown', event => {
      if (event.key !== 'Delete' && event.key !== 'Backspace') return;
      event.preventDefault();
      event.stopPropagation();
      empty(vacate);
    });
  }
  function empty(vacate) {
    edit(vacate());
    options.onToast?.(vacate.removes ? 'Removed ' + vacate.label : 'Emptied ' + vacate.label + '. Drag a block in, or click it to choose one.', {undo: true});
  }
  function moveInto(t, from, copy) {
    const into = t.slot.dataset.slot;
    const encloses = t.node.start <= from.node?.start && from.node.end <= t.node.end;
    if (copy || !from.vacate || encloses) {
      t.replace(from.text);
      if (from.vacate) options.onToast?.((encloses ? 'Moved ' : 'Copied ') + from.title + ' to ' + into, {undo: true});
      return;
    }
    edit([stamp(t.node, from.text), ...from.vacate()]);
    options.onToast?.('Moved ' + from.title + ' to ' + into + (from.vacate.removes ? '' : '. ' + human(from.vacate.label) + ' is empty now.'), {undo: true});
  }
  // Out on the canvas, a block becomes a value of its own, declared just above the statement it left.
  function moveOut(from, point, copy) {
    const sig = from.node.kind === 'Call' && allCalls.get(from.node.label);
    const name = freshName(from.node.kind === 'Call' ? NAME_FOR[sig?.result] || from.node.label : 'items');
    const owner = statements.find(s => s.start === from.at);
    const start = owner ? noteRange(owner).start : from.at;
    placeNew(name, point);
    const edits = [{start, end: start, text: 'let ' + name + ' = ' + from.text + '\n'}];
    if (!copy && from.vacate) edits.push(...from.vacate());
    edit(edits);
    options.onToast?.(copy || !from.vacate ? 'Copied ' + from.title + ' to a new value, ' + name :
      'Moved ' + from.title + ' out to ' + name + (from.vacate.removes ? '' : '. Drag ' + name + ' back, or choose another block for ' + from.vacate.label + '.'), {undo: true});
  }
  function arm(sig, toggle = true) {
    if (toggle && armed && sig && armed.name === sig.name) sig = null;
    close();
    disarm();
    if (!sig) return;
    armed = resolve(sig);
    const count = activate(t => accepts(armed.result, t.expected, null, t.context));
    banner = el('div', 'place-banner');
    banner.setAttribute('role', 'status');
    const chip = miniBlock(armed, 'pal-block banner-block');
    chip.tabIndex = -1;
    const text = el('span', 'place-text', count ? 'Click a glowing input or empty canvas, or press Tab and Enter.' :
      'No open input takes a ' + (armed.result || 'value') + '. Click empty canvas to place it there.');
    const add = button('', () => placeArmed(), 'btn primary small');
    add.append(icon('plus'), 'New value');
    const cancel = button('Cancel', () => { disarm(); options.onArm?.(null); }, 'btn ghost small');
    banner.append(chip, text, add, cancel);
    (options.overlay || host).prepend(banner);
    options.onArm?.(armed);
    options.onHelp?.(armed, true);
  }
  function disarm() {
    armed = null;
    banner?.remove();
    banner = null;
    host.classList.remove('placing');
    for (const {slot} of sockets) { delete slot.dataset.active; delete slot.dataset.over; }
    hover(null);
    refuse(null);
  }
  function placeArmed(t, point, sig = armed) {
    if (!sig) return;
    disarm();
    options.onArm?.(null);
    if (t) t.replace(replacementCall(sig, t.at, t.node), sig.module);
    else if (!sig.module && operations[sig.name] && !point) addCheck(sig.name);
    else addDeclaration(callValue(sig, chars.length), sig.module, point);
  }
  const emptyCanvas = node => node === host || node === board || node?.classList?.contains('board');
  const activeSlot = node => {
    let slot = node?.closest?.('.slot');
    while (slot && !slot.dataset.active) slot = slot.parentElement?.closest('.slot');
    return slot && host.contains(slot) ? slot : null;
  };
  listen(host, 'click', event => {
    if (!armed || event.target.closest('.place-banner, .pop')) return;
    const slot = activeSlot(event.target);
    event.preventDefault();
    event.stopPropagation();
    if (slot) placeArmed(target(slot));
    else if (emptyCanvas(event.target)) placeArmed(undefined, boardPoint(event.clientX, event.clientY));
    else { disarm(); options.onArm?.(null); }
  }, {capture: true});
  // A dragged value snaps to the nearest input that takes it, within this many pixels.
  const SNAP = 44;
  function nearestSlot(x, y) {
    let best = null;
    let distance = SNAP;
    for (const {slot} of sockets) {
      if (!slot.dataset.active) continue;
      const box = slot.getBoundingClientRect();
      const d = Math.hypot(Math.max(box.left - x, 0, x - box.right), Math.max(box.top - y, 0, y - box.bottom));
      if (d < distance) { best = slot; distance = d; }
    }
    return best;
  }
  const dragFamily = () => dragging?.family || (armed && familyOf(armed.result));
  const dragTitle = () => dragging?.title || (armed && human(armed.name)) || dragging?.text || 'this value';
  // The input under a dragged value lifts and shows the value snapped into it.
  function hover(slot) {
    if (slot === overSlot) return;
    if (overSlot) {
      delete overSlot.dataset.over;
      overSlot.querySelector(':scope > .snap-ghost')?.remove();
    }
    overSlot = slot;
    if (!slot) return;
    slot.dataset.over = 'true';
    const family = dragFamily();
    const ghost = el('span', 'snap-ghost', dragTitle());
    ghost.dataset.family = family;
    keyed(ghost, family);
    slot.append(ghost);
  }
  // An input that does not take the dragged value says why, in terms of its connector.
  function refuse(slot) {
    if (slot === nopeSlot) return;
    if (nopeSlot) delete nopeSlot.dataset.nope;
    if (nopeSlot && bubble?.anchor === nopeSlot) hideBubble();
    nopeSlot = slot;
    if (!slot) return;
    slot.dataset.nope = 'true';
    const need = familyOf(slot.dataset.accepts);
    const have = dragFamily();
    const named = family => family === 'value' ? (slot.dataset.accepts === 'string' ? 'text' : 'a number') :
      'a ' + (FAMILIES[family] || 'value').toLowerCase() + (SHAPES[family] ? ' (' + SHAPES[family] + ' connector)' : '');
    showBubble(slot, need === have ?
      'Same connector, but this input needs a ' + slot.dataset.accepts + ' declared above it.' :
      'This input takes ' + named(need) + '. ' + dragTitle() + ' is ' + named(have) + '.', 'warning');
  }
  // Problems --------------------------------------------------------------------
  const lineStarts = [0];
  for (const line of source.split('\n')) lineStarts.push(lineStarts.at(-1) + Array.from(line).length + 1);
  const offset = (line, column) => (lineStarts[line - 1] ?? chars.length) + column - 1;
  function nodeFor(span) {
    const position = offset(span.line, span.column);
    const end = offset(span.end_line, span.end_column);
    const stack = stacks.find(({s}) => s.start <= position && position <= s.end);
    if (!stack) return null;
    let found = stack.card;
    for (const node of stack.card.querySelectorAll('.blk')) {
      if (+node.dataset.start <= position && end <= +node.dataset.end) found = node;
    }
    return found;
  }
  function decorate() {
    const groups = new Map();
    for (const diagnostic of options.diagnostics || []) {
      // A value that fails only because it uses a broken one waits quietly, naming the cause.
      if (diagnostic.cause) {
        const card = nodeFor(diagnostic.source)?.closest('.stack');
        if (!card || card.querySelector('.hat-waiting')) continue;
        card.classList.add('waiting');
        const chip = button('waits for ' + diagnostic.cause, () => focusName(diagnostic.cause), 'hat-waiting');
        chip.title = (card.dataset.name || 'This check') + ' cannot be checked until ' + diagnostic.cause + ' is fixed';
        card.querySelector('.hat-issues').before(chip);
        continue;
      }
      const node = nodeFor(diagnostic.source);
      if (!node) continue;
      if (!groups.has(node)) groups.set(node, []);
      groups.get(node).push(diagnostic);
    }
    for (const [node, list] of groups) {
      const severity = list.some(d => d.severity === 'error') ? 'error' : 'warning';
      node.classList.add('has-issue', 'issue-' + severity);
      const badge = button(list.length > 1 ? String(list.length) : '!', () => issuePopover(badge, list), 'issue-badge issue-' + severity);
      badge.setAttribute('aria-label', plural(list.length, severity === 'error' ? 'error' : 'open obligation') + ': ' + list.map(d => d.message).join(' '));
      badge.title = list.map(d => codeTitle(d.code) + ': ' + d.message).join('\n');
      if (options.shake) badge.classList.add('shake');
      (node.matches('.stack') ? node.querySelector('.hat') : node).append(badge);
      const card = node.closest('.stack');
      card.classList.add('has-issue', 'issue-' + severity);
      const count = card.querySelector('.hat-issues');
      count.hidden = false;
      count.dataset.severity = card.classList.contains('issue-error') ? 'error' : 'warning';
      count.textContent = String((+count.dataset.count || 0) + list.length);
      count.dataset.count = count.textContent;
      count.title = count.textContent + ' issue(s) in this block';
    }
  }
  function issuePopover(anchor, list) {
    const severity = list.some(d => d.severity === 'error') ? 'error' : 'warning';
    const body = open(anchor, list.length > 1 ? plural(list.length, 'issue') : codeTitle(list[0].code), {cls: 'issue-pop issue-' + severity,
      subtitle: (severity === 'error' ? 'Error' : 'Open obligation: the file is valid, the claim is not yet established') + ' · line ' + list[0].source.line});
    for (const diagnostic of list) {
      const item = el('div', 'issue-item');
      if (list.length > 1) item.append(el('strong', '', codeTitle(diagnostic.code)));
      item.append(messageBlock(diagnostic.message, 'pop-text'));
      for (const related of diagnostic.related || []) {
        const go = button('', () => { close(); reveal(related.source); }, 'issue-related');
        go.append(icon('target'), el('span', '', 'Line ' + related.source.line + ' · ' + related.message));
        item.append(go);
      }
      body.append(item);
    }
    const found = fixesAt(anchor);
    if (found) fixList(body, found, close);
    if (options.onShowProblems) {
      const actions = el('div', 'pop-actions');
      actions.append(button('Open in Problems', () => { close(); options.onShowProblems(); }, 'btn small'));
      body.append(actions);
    }
    body.closest('.pop').querySelector('.pop-close').focus();
  }
  function flash(node) {
    if (!node) return;
    node.classList.remove('flash');
    void node.offsetWidth;
    node.classList.add('flash');
  }
  function reveal(span) {
    const node = nodeFor(span);
    if (!node) return null;
    const card = node.closest('.stack');
    const name = card?.dataset.name;
    if (name && folded.has(name)) toggleFold(stacks.find(x => x.card === card).s, card);
    scrollInside(host, node, 'center');
    flash(node);
    const focusable = node.matches('input,select,button') ? node : node.querySelector('input,select,button');
    (focusable || card)?.focus({preventScroll: true});
    return node;
  }
  // The checked derivation of one declaration, fetched from Python when asked for.
  function whyPopover(anchor, name) {
    const body = open(anchor, 'Why ' + name + ' fits', {cls: 'why-pop', subtitle: 'The contract check, step by step'});
    const wait = el('p', 'pop-text', 'Asking StatClaim…');
    body.append(wait);
    const current = pop;
    options.onExplain(name).then(entries => {
      if (pop !== current) return;
      wait.remove();
      if (!entries?.length) body.append(el('p', 'pop-text', 'There is no contract to explain for ' + name + '. Models, designs and nulls have none of their own.'));
      for (const entry of entries || []) body.append(derivationView(entry));
      place(current, anchor);
    }, error => {
      if (pop === current) wait.textContent = error.message;
    });
  }
  function focusName(name) {
    const index = statements.findIndex(st => st.name === name);
    if (index >= 0) focusStatement(index);
  }
  // Opens the chooser of the input at a span, such as an empty input.
  function pickAt(span) {
    const position = offset(span.line, span.column);
    const found = sockets.find(t => !t.root && t.node.start === position && t.pick);
    if (!found) return false;
    const card = found.slot.closest('.stack');
    if (card?.dataset.name && folded.has(card.dataset.name)) {
      toggleFold(stacks.find(x => x.card === card).s, card);
      return pickAt(span);
    }
    scrollInside(host, found.slot, 'center');
    found.pick();
    return true;
  }
  function focusStatement(i) {
    const entry = stacks.find(x => x.s === statements[i]);
    if (!entry) return;
    if (entry.s.name && folded.has(entry.s.name)) toggleFold(entry.s, entry.card);
    scrollInside(host, entry.card);
    entry.card.focus({preventScroll: true});
    flash(entry.card);
  }

  // Free placement -------------------------------------------------------------
  const zoomOf = () => parseFloat(board && window.getComputedStyle?.(board).zoom) || 1;
  function boardPoint(clientX, clientY) {
    const rect = board.getBoundingClientRect();
    const zoom = zoomOf();
    return {x: Math.max(0, Math.round((clientX - rect.left) / zoom)), y: Math.max(0, Math.round((clientY - rect.top) / zoom))};
  }
  function measure(entry) {
    const {card} = entry;
    const note = card.querySelector(':scope > .stack-note');
    const extra = note && note.offsetLeft >= card.offsetWidth ? note.offsetLeft + note.offsetWidth - card.offsetWidth : 0;
    entry.w = card.offsetWidth + extra;
    entry.h = card.offsetHeight;
  }
  function put(entry, x, y) {
    entry.x = x;
    entry.y = y;
    entry.card.style.left = x + 'px';
    entry.card.style.top = y + 'px';
  }
  const overlap = (a, b) => a.x < b.x + b.w + 16 && b.x < a.x + a.w + 16 && a.y < b.y + b.h + 16 && b.y < a.y + a.h + 16;
  // Stacks keep their places; one that would overlap another slides down below it.
  function arrange(last) {
    for (const entry of stacks) measure(entry);
    if (!layout) {
      let y = PAD;
      for (const entry of stacks) { put(entry, PAD, y); y += entry.h + GAP; }
    } else {
      const placed = stacks.filter(e => layout[keyOf(e.s)]);
      for (const entry of placed) [entry.x, entry.y] = layout[keyOf(entry.s)];
      const order = placed.filter(e => e !== last).sort((a, b) => a.y - b.y || a.x - b.x);
      if (last && placed.includes(last)) order.push(last);
      const done = [];
      for (const entry of order) {
        let moved = true;
        while (moved) {
          moved = false;
          for (const other of done) if (overlap(entry, other)) { entry.y = other.y + other.h + GAP; moved = true; }
        }
        done.push(entry);
        put(entry, entry.x, entry.y);
      }
      let bottom = Math.max(PAD - GAP, ...done.map(e => e.y + e.h));
      for (const entry of stacks.filter(e => !layout[keyOf(e.s)])) { put(entry, PAD, bottom + GAP); bottom = entry.y + entry.h; }
    }
    sizeBoard();
  }
  function sizeBoard() {
    if (!board) return;
    board.style.width = Math.max(0, ...stacks.map(e => e.x + e.w)) + 240 + 'px';
    board.style.height = Math.max(0, ...stacks.map(e => e.y + e.h)) + 140 + 'px';
  }
  function glide(last) {
    if (!board) return;
    board.classList.add('arranging');
    arrange(last);
    drawWires();
    clearTimeout(board.glideTimer);
    board.glideTimer = setTimeout(() => { board?.classList.remove('arranging'); drawWires(); }, 420);
  }
  // Wires run from a value's stack to each input that uses it: on hover, or always when links are shown.
  function drawWires() {
    if (!board) return;
    if (!wireLayer?.isConnected) {
      wireLayer = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      wireLayer.setAttribute('class', 'wires');
      wireLayer.setAttribute('aria-hidden', 'true');
      board.prepend(wireLayer);
    }
    wireLayer.replaceChildren();
    board.classList.toggle('wired', wiresOn);
    if (!wiresOn && !hoverCard) return;
    const zoom = zoomOf();
    const origin = board.getBoundingClientRect();
    const local = rect => ({x: (rect.left - origin.left) / zoom, y: (rect.top - origin.top) / zoom, h: rect.height / zoom});
    for (const pill of board.querySelectorAll('.pill[data-ref]')) {
      const source = stacks.find(e => e.s.name === pill.dataset.ref);
      const target = pill.closest('.stack');
      if (!source || !target || target === source.card) continue;
      const hot = hoverCard && (hoverCard === source.card || hoverCard === target);
      if (!wiresOn && !hot) continue;
      const visible = pill.offsetParent !== null;
      const end = local((visible ? pill : target.querySelector('.hat')).getBoundingClientRect());
      const width = source.card.offsetWidth;
      const to = {x: end.x, y: end.y + end.h / 2};
      const right = to.x > source.x + width + 24;
      const from = right ? {x: source.x + width, y: source.y + 20} : {x: source.x, y: source.y + 20};
      const bend = right ? Math.max(48, (to.x - from.x) / 2) : 34 + Math.min(110, Math.abs(to.y - from.y) * .12);
      const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      path.setAttribute('d', 'M' + from.x + ' ' + from.y + ' C' + (from.x + (right ? bend : -bend)) + ' ' + from.y + ' ' +
        (to.x - bend) + ' ' + to.y + ' ' + to.x + ' ' + to.y);
      path.setAttribute('class', 'wire' + (hot ? ' hot' : ''));
      path.dataset.family = source.card.dataset.family;
      const dot = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      dot.setAttribute('cx', to.x);
      dot.setAttribute('cy', to.y);
      dot.setAttribute('r', hot ? 4 : 3);
      dot.setAttribute('class', 'wire-end' + (hot ? ' hot' : ''));
      dot.dataset.family = source.card.dataset.family;
      wireLayer.append(path, dot);
    }
  }
  const positions = () => Object.fromEntries(stacks.map(e => [keyOf(e.s), [Math.round(e.x), Math.round(e.y)]]));
  function saveLayout(map, extra) {
    layout = map;
    options.onLayout?.(map, extra);
  }
  function placeNew(key, point) {
    saveLayout({...(layout || positions()), [key]: [Math.round(point.x), Math.round(point.y)]});
  }
  function near(s) {
    const entry = layout && stacks.find(e => e.s === s);
    return entry ? {x: entry.x + entry.w + 48, y: entry.y} : null;
  }
  function cleanUp() {
    close();
    saveLayout(null, {commit: true, label: 'Tidied into one column'});
    glide();
    options.onToast?.('Tidied the blocks into one column', {undo: true});
  }
  // Each value sits one column to the right of the values it uses, so a study reads left to right:
  // models, then designs and nulls, then analyses, then claims and checks.
  function arrangeByFlow() {
    close();
    if (!board) return;
    for (const entry of stacks) measure(entry);
    const byName = new Map(statements.filter(st => st.name).map(st => [st.name, st]));
    const depth = new Map();
    const uses = st => {
      const found = new Set();
      walk(st.expression, n => { if (n.kind === 'Reference' && byName.has(n.label) && byName.get(n.label) !== st) found.add(byName.get(n.label)); });
      return [...found];
    };
    const depthOf = st => {
      if (depth.has(st)) return depth.get(st);
      depth.set(st, 0);
      const value = Math.max(0, ...uses(st).map(other => depthOf(other) + 1));
      depth.set(st, value);
      return value;
    };
    const columns = [];
    for (const entry of stacks) (columns[depthOf(entry.s)] ||= []).push(entry);
    const map = {};
    const centre = entry => {
      const inputs = uses(entry.s).map(other => map[keyOf(other)] && stacks.find(e => e.s === other)).filter(Boolean);
      return inputs.length ? inputs.reduce((sum, e) => sum + map[keyOf(e.s)][1] + e.h / 2, 0) / inputs.length : Infinity;
    };
    let x = PAD;
    for (const column of columns) {
      if (!column) continue;
      // Within a column, a value sits level with what it uses, so links cross less.
      const order = column.map((entry, i) => ({entry, i, at: centre(entry)})).sort((a, b) => a.at - b.at || a.i - b.i);
      let y = PAD;
      for (const {entry} of order) {
        map[keyOf(entry.s)] = [x, y];
        y += entry.h + GAP;
      }
      x += Math.max(...column.map(e => e.w)) + 72;
    }
    saveLayout(map, {commit: true, label: 'Arranged by flow'});
    glide();
    options.onToast?.('Arranged by flow: each value sits to the right of what it uses', {undo: true});
  }
  // The size of everything on the board at 100%, for zoom to fit.
  function bounds() {
    for (const entry of stacks) measure(entry);
    return {w: Math.max(0, ...stacks.map(e => e.x + e.w)) + PAD, h: Math.max(0, ...stacks.map(e => e.y + e.h)) + PAD};
  }
  function foldAll(collapse) {
    for (const {s, card} of stacks) {
      if (!s.name) continue;
      if (collapse) folded.add(s.name); else folded.delete(s.name);
      paintFold(s, card);
    }
    glide();
  }
  const inside = (node, event) => {
    const rect = node.getBoundingClientRect();
    return event.clientX >= rect.left && event.clientX <= rect.right && event.clientY >= rect.top && event.clientY <= rect.bottom;
  };
  // Drag a stack by its hat or body, like a Scratch script. Dropping it on the palette deletes it.
  let movedAt = 0;
  // A drag that ends over a button must not also click it.
  listen(host, 'click', event => {
    if (Date.now() - movedAt < 120) { event.preventDefault(); event.stopImmediatePropagation(); }
  }, {capture: true});
  function startMove(event, entry) {
    if (event.button !== 0 || !board) return;
    const title = event.target.closest('.blk-root > .blk-head .blk-name');
    if (!title && event.target.closest('button, input, select, textarea, label, .slot:not(.slot-root), .stack-note')) return;
    if (event.pointerType === 'touch' && !event.target.closest('.hat')) return;
    event.preventDefault();
    const zoom = zoomOf();
    const start = {x: event.clientX, y: event.clientY, left: entry.x, top: entry.y};
    const trash = options.trash;
    let moving = false;
    let overTrash = false;
    const drag = new AbortController();
    const end = () => {
      drag.abort();
      entry.card.classList.remove('moving', 'trashing');
      host.classList.remove('moving-stack');
      trash?.classList.remove('trash-over');
    };
    document.addEventListener('pointermove', e => {
      const dx = (e.clientX - start.x) / zoom;
      const dy = (e.clientY - start.y) / zoom;
      if (!moving) {
        if (Math.hypot(dx, dy) < 5) return;
        moving = true;
        close();
        entry.card.classList.add('moving');
        host.classList.add('moving-stack');
        entry.card.style.zIndex = String(++zTop);
      }
      put(entry, Math.max(0, start.left + dx), Math.max(0, start.top + dy));
      drawWires();
      overTrash = Boolean(trash) && inside(trash, e);
      trash?.classList.toggle('trash-over', overTrash);
      entry.card.classList.toggle('trashing', overTrash);
      const view = host.getBoundingClientRect();
      if (e.clientY > view.bottom - 36) host.scrollTop += 14;
      else if (e.clientY < view.top + 36) host.scrollTop -= 14;
      if (e.clientX > view.right - 36) host.scrollLeft += 14;
      else if (e.clientX < view.left + 36 && !overTrash) host.scrollLeft -= 14;
      sizeBoard();
    }, {signal: drag.signal});
    document.addEventListener('pointercancel', () => { end(); if (moving) { put(entry, start.left, start.top); sizeBoard(); } }, {signal: drag.signal});
    document.addEventListener('pointerup', () => {
      const dropped = moving;
      const deleting = overTrash;
      end();
      if (!dropped) return;
      movedAt = Date.now();
      if (deleting) {
        const used = [...(users.get(entry.s.name) || [])].map(i => statements[i].name || 'a check');
        if (entry.s.name && used.length) {
          options.onToast?.('Kept ' + entry.s.name + ': ' + used.join(', ') + (used.length === 1 ? ' still uses it.' : ' still use it.'));
          board.classList.add('arranging');
          put(entry, start.left, start.top);
          setTimeout(() => board?.classList.remove('arranging'), 420);
        } else remove(entry.s);
        return;
      }
      layout = positions();
      glide(entry);
      saveLayout(positions(), {commit: true, label: 'Moved ' + (entry.s.name || 'a check')});
    }, {signal: drag.signal});
  }
  // Keyboard: arrows move between stacks, Option+arrows move a stack, Enter opens its menu.
  function nudge(entry, dx, dy) {
    if (!layout) layout = positions();
    layout = {...positions(), [keyOf(entry.s)]: [Math.max(0, Math.round(entry.x + dx)), Math.max(0, Math.round(entry.y + dy))]};
    glide(entry);
    saveLayout(positions(), {commit: true, coalesce: true, label: 'Nudged ' + (entry.s.name || 'a check')});
    scrollInside(host, entry.card);
  }
  function stackKeys(event, entry) {
    if (event.target !== entry.card) return;
    const index = stacks.indexOf(entry);
    const step = event.shiftKey ? 80 : 20;
    const moves = {ArrowLeft: [-step, 0], ArrowRight: [step, 0], ArrowUp: [0, -step], ArrowDown: [0, step]};
    if (event.altKey && moves[event.key]) {
      event.preventDefault();
      nudge(entry, ...moves[event.key]);
    } else if (event.key === 'ArrowDown' || event.key === 'ArrowUp') {
      event.preventDefault();
      const next = stacks[index + (event.key === 'ArrowDown' ? 1 : -1)];
      if (next) { next.card.focus({preventScroll: true}); scrollInside(host, next.card); }
    } else if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      stackMenu(entry.card.querySelector('.hat-btn'), entry.s, entry.card);
    } else if (event.key === 'F2' && entry.s.name) {
      event.preventDefault();
      startRename(entry.s, entry.card.querySelector('.stack-name'));
    } else if (event.key === 'Delete' || event.key === 'Backspace') {
      event.preventDefault();
      const used = [...(users.get(entry.s.name) || [])].map(i => statements[i].name || 'a check');
      if (entry.s.name && used.length) options.onToast?.('Kept ' + entry.s.name + ': ' + used.join(', ') + (used.length === 1 ? ' still uses it.' : ' still use it.'));
      else remove(entry.s);
    }
  }
  const pointAnchor = (x, y) => ({
    isConnected: true, contains: () => false, focus() {},
    getBoundingClientRect: () => ({left: x, right: x, top: y, bottom: y, width: 0, height: 0}),
  });
  function canvasMenu(anchor, point) {
    const body = open(anchor, 'Canvas', {cls: 'menu', subtitle: 'Right-click a block for its own menu'});
    const menu = el('div', 'menu-items');
    body.append(menu);
    menuItem(menu, 'New value here…', 'plus', () => chooser(anchor, 'Add a new value', null, chars.length, (v, m) => addDeclaration(v, m, point)));
    for (const name of Object.keys(operations)) {
      menuItem(menu, 'Add a ' + human(name) + ' check here', name === 'verify' ? 'check' : 'spark', () => addCheck(name, point));
    }
    menuItem(menu, 'Arrange by flow', 'flow', arrangeByFlow, {note: 'left to right'});
    menuItem(menu, 'Clean up blocks', 'grid', cleanUp, {disabled: !layout, note: layout ? 'file order' : 'already tidy'});
    menuItem(menu, 'Collapse all', 'collapse', () => { close(); foldAll(true); });
    menuItem(menu, 'Expand all', 'expand', () => { close(); foldAll(false); });
    menu.querySelector('button:not(:disabled)')?.focus();
  }
  listen(host, 'contextmenu', event => {
    if (event.target.closest('input, textarea, .pop')) return;
    event.preventDefault();
    const keyboard = !event.clientX && !event.clientY;
    const anchor = keyboard ? event.target : pointAnchor(event.clientX, event.clientY);
    for (let node = event.target; node && node !== host; node = node.parentElement) {
      if (node.contextMenu) return node.contextMenu(anchor);
    }
    if (board) canvasMenu(anchor, keyboard ? {x: PAD, y: PAD} : boardPoint(event.clientX, event.clientY));
  });

  // Layout --------------------------------------------------------------------
  function starter() {
    const box = el('div', 'starter');
    box.append(el('div', 'starter-art'));
    box.append(el('h2', '', 'Start a study'));
    // The quickest start is a design: a few questions, and the blocks arrive connected.
    if (options.onDesign) {
      box.append(el('p', '', 'Pick a family of designs. A few questions build a study that compiles, and every block can be changed.'));
      const families = el('div', 'starter-families');
      for (const family of DESIGN_FAMILIES) {
        const chip = button('', () => options.onDesign({family: family.id}), 'starter-family');
        chip.dataset.family = family.family;
        const badge = el('span', 'starter-family-glyph');
        badge.append(glyph(family.glyph));
        const words = el('span', 'starter-family-words');
        words.append(el('strong', '', family.title), el('span', '', DESIGNS.filter(d => d.family === family.id).length + ' designs'));
        chip.append(badge, words);
        chip.title = family.detail;
        families.append(chip);
      }
      box.append(families, el('p', 'starter-or', 'or build it from blocks'));
    } else box.append(el('p', '', 'Pick a study model to begin. Then connect a design, a null hypothesis and an analysis, and ask StatClaim to verify a claim.'));
    const picks = el('div', 'starter-picks');
    for (const name of ['two_arm_binomial', 'two_arm_continuous', 'one_arm_binomial', 'two_arm_survival']) {
      const sig = allCalls.get(name);
      if (!sig) continue;
      const item = miniBlock(sig, 'pal-block starter-block');
      item.addEventListener('click', () => addDeclaration(callValue(sig, chars.length), sig.module));
      item.title = sig.typed_signature;
      picks.append(item);
    }
    box.append(picks, el('p', 'starter-hint', 'Or drag any block from the palette onto this canvas.'));
    return box;
  }
  function addBar() {
    const bar = el('div', 'add-bar');
    bar.setAttribute('role', 'toolbar');
    bar.setAttribute('aria-label', 'Add to the study');
    const add = button('', () => chooser(add, 'Add a new value', null, chars.length, addDeclaration), 'btn add-main');
    add.append(icon('plus'), 'New value');
    add.title = 'Add a named value (let …)';
    const check = button('', () => {
      const body = open(check, 'Add a check', {cls: 'menu', family: 'run', subtitle: 'Ask StatClaim to verify or calculate'});
      const menu = el('div', 'menu-items');
      body.append(menu);
      for (const name of Object.keys(operations)) {
        menuItem(menu, human(name), name === 'verify' ? 'check' : 'spark', () => addCheck(name), {note: allCalls.get(name)?.typed_signature});
      }
      menu.querySelector('button')?.focus();
    }, 'btn');
    check.append(icon('play'), 'Add check');
    const used = (options.uses || []).length;
    const mods = button('', () => {
      const body = open(mods, 'Study modules', {subtitle: 'A module makes its blocks available. Blocks add their module when you use them.'});
      const listBox = el('div', 'module-list');
      for (const module of Object.keys(modules)) {
        const use = options.uses?.find(u => u.name === module);
        const row = el('label', 'module-row');
        const toggle = el('input');
        toggle.type = 'checkbox';
        toggle.checked = Boolean(use);
        toggle.addEventListener('change', () => use ? change(use.start, use.end + (chars[use.end] === '\n' ? 1 : 0), '') : edit([useEdit(module)]));
        const info = options.module_info?.[module];
        const text = el('span', 'module-text');
        text.append(el('strong', '', module));
        if (info?.classification) text.append(el('small', '', info.classification));
        row.append(toggle, text);
        if (info?.support) row.title = info.support;
        listBox.append(row);
      }
      body.append(listBox);
    }, 'btn ghost');
    mods.append(icon('book'), 'Modules · ' + used);
    bar.append(add, check, mods);
    return bar;
  }
  function draw() {
    close();
    // Emptying the canvas drops its scroll. It goes back at once, not smoothly, so an edit
    // does not jump to the top and glide back.
    const keep = options.scroll || {top: host.scrollTop, left: host.scrollLeft};
    host.replaceChildren();
    sockets.length = stacks.length = 0;
    known.clear();
    host.classList.toggle('is-empty', !statements.length);
    host.classList.toggle('entering', Boolean(options.enter));
    const intro = headerNote();
    if (intro.text) {
      const card = button('', () => editNote(card, intro, 'Study description'), 'doc-intro');
      card.append(icon('note'), el('span', '', prose(intro.text)));
      card.title = 'Edit the study description';
      host.append(card);
    }
    board = null;
    if (statements.length) {
      board = el('div', 'board');
      host.append(board);
      statements.forEach((s, i) => {
        board.append(drawStack(s, i));
        if (s.name) known.set(s.name, bindings[s.name]?.type || typeOf(s.expression));
      });
      arrange();
      drawWires();
    } else host.append(starter());
    if (options.dock) options.dock.replaceChildren(addBar());
    else host.append(addBar());
    decorate();
    if (host.scrollTo) host.scrollTo({...keep, behavior: 'instant'});
    else { host.scrollTop = keep.top; host.scrollLeft = keep.left; }
    const range = options.highlight;
    if (range) {
      let best = null;
      for (const node of host.querySelectorAll('.stack, .blk')) {
        const start = +node.dataset.start;
        const end = +node.dataset.end;
        if (start <= range.start && range.end <= end && (!best || end - start <= +best.dataset.end - +best.dataset.start)) best = node;
      }
      if (best && options.refocus) {
        const control = best.matches('.stack') ? best :
          best.querySelector(':scope > .pill, :scope > .blk-head > .blk-name, :scope > .lit-input, :scope > .lit-select, :scope > input') || best.closest('.stack');
        control?.focus({preventScroll: true});
      }
      if (best && (best.matches('.blk') || range.end - range.start < 400)) {
        flash(best);
        const rect = best.getBoundingClientRect?.();
        const view = host.getBoundingClientRect?.();
        if (rect && view && (rect.bottom > view.bottom || rect.top < view.top)) scrollInside(host, best);
      }
    }
  }
  draw();
  listen(document, 'keydown', event => {
    if (event.key !== 'Escape') return;
    if (pop) close(true);
    else if (armed) { disarm(); options.onArm?.(null); }
    else if (selected && !event.target.closest?.('input, textarea, select')) select(null);
  });
  // Clicking empty canvas clears the selection.
  listen(host, 'pointerdown', event => { if (!armed && emptyCanvas(event.target)) select(null); });
  // A selection whose value is gone, after a rename or a delete, ends.
  if (selected && !declarations.some(s => s.name === selected)) queueMicrotask(() => select(null));
  // Leave quietly: a later mount may belong to another editor.
  teardown = () => { life.abort(); pop?.remove(); pop = null; hideBubble(); banner?.remove(); };
  return {
    focusStatement,
    focusName,
    pick: pickAt,
    reveal,
    arm: sig => arm(sig),
    disarm: () => { disarm(); options.onArm?.(null); },
    grab(sig, event, element) { press(event, {sig: resolve(sig), title: human(sig.name), family: familyOf(sig.result)}, element); },
    peek(span, on) { nodeFor(span)?.classList.toggle('peek', on); },
    selected: () => selected,
    select: name => select(stacks.find(x => x.s.name === name) || null),
    showFits(name, fits) {
      if (name !== selected) return;
      selectedFits = fits;
      paintFits();
    },
    foldAll,
    cleanUp,
    arrangeByFlow,
    bounds,
    relayout: () => glide(),
    setWires(on) { wiresOn = on; drawWires(); },
    fixes: span => fixesAt(nodeFor(span)),
    destroy: () => teardown?.(),
  };
}
