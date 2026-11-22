// The block palette: a category rail and the blocks of each module, like Scratch.
import { el, button, human, icon, iconButton, familyOf, plural, scrollInside, keyShape, keyGlyph } from './ui.js';

const CATEGORIES = [
  ['Models and hypotheses', 'Study', 'study'],
  ['Study designs', 'Design', 'design'],
  ['Observational studies', 'Obser\u00advational', 'study'],
  ['Analyses and claims', 'Analyses', 'analysis'],
  ['Cited analyses', 'Cited', 'analysis'],
  ['Declared analyses', 'Declared', 'analysis'],
  ['Multiplicity and composition', 'Families', 'family'],
  ['Adaptive designs', 'Adaptive', 'design'],
  ['Study planning', 'Planning', 'planning'],
  ['Operations', 'Checks', 'run'],
];
const TIERS = {'Cited analyses': 'cited', 'Declared analyses': 'declared'};

// One entry per constructor name and category; shared constructors appear once.
export function libraryEntries(catalog) {
  const order = new Map(CATEGORIES.map(([name], i) => [name, i]));
  const sections = new Map();
  const section = name => {
    if (!sections.has(name)) {
      const known = CATEGORIES.find(c => c[0] === name);
      sections.set(name, {name, short: known?.[1] || name, family: known?.[2] || 'other', modules: new Map(), seen: new Set()});
    }
    return sections.get(name);
  };
  for (const [module, constructors] of Object.entries(catalog.modules || {}).sort(([a], [b]) => a.localeCompare(b))) {
    const info = catalog.module_info?.[module] || {};
    const target = section(info.classification || 'Other modules');
    for (const [name, sig] of Object.entries(constructors)) {
      if (target.seen.has(name)) continue;
      target.seen.add(name);
      if (!target.modules.has(module)) target.modules.set(module, []);
      target.modules.get(module).push({...sig, name, module, tier: TIERS[info.classification], support: info.support,
        classification: info.classification});
    }
  }
  const operations = section('Operations');
  operations.modules.set('', Object.entries(catalog.operations || {}).map(([name, sig]) => ({...sig, name, module: undefined})));
  return [...sections.values()].sort((a, b) => (order.get(a.name) ?? 99) - (order.get(b.name) ?? 99));
}

export function moduleTitle(module) {
  if (!module) return 'Run a request';
  return human(module.split('.').at(-1));
}

export function miniBlock(sig, cls = 'pal-block') {
  const node = button('', null, cls);
  node.dataset.family = familyOf(sig.result);
  const key = keyShape(node.dataset.family);
  if (key) node.append(key);
  const name = el('span', 'pal-name', human(sig.name));
  node.append(name);
  // Each required input shows the connector it takes.
  for (const param of Object.keys(sig.parameters || {}).filter(p => !(sig.optional || []).includes(p)).slice(0, 3)) {
    const hole = el('span', 'pal-hole', human(param));
    hole.dataset.family = familyOf(sig.parameters[param]);
    hole.dataset.param = param;
    const glyph = keyGlyph(hole.dataset.family, 'key key-chip');
    if (glyph) hole.prepend(glyph);
    node.append(hole);
  }
  if (sig.tier) {
    const badge = el('span', 'tier tier-' + sig.tier, sig.tier);
    badge.title = sig.tier === 'cited' ? 'Guarantee cited from the literature, not proved here' :
      'Guarantee declared by the author: the weakest evidence';
    node.append(badge);
  }
  return node;
}

export function mountPalette(root, catalog, handlers) {
  const sections = libraryEntries(catalog);
  const rail = el('nav', 'rail');
  rail.setAttribute('aria-label', 'Block categories');
  const panel = el('div', 'palette');
  const searchWrap = el('label', 'pal-search');
  searchWrap.append(icon('search'));
  const search = el('input');
  search.id = 'paletteSearch';
  search.type = 'search';
  search.placeholder = 'Search blocks   /';
  search.setAttribute('aria-label', 'Search blocks');
  searchWrap.append(search);
  const list = el('div', 'pal-list');
  list.setAttribute('aria-label', 'Blocks');
  const empty = el('p', 'pal-empty', 'No block matches this search.');
  empty.hidden = true;
  // Hints for the selected value: what takes it glows, the rest fades.
  const strip = el('div', 'pal-hint');
  strip.hidden = true;
  strip.setAttribute('role', 'status');
  panel.append(searchWrap, strip, list);
  root.replaceChildren(rail, panel);

  const items = [];
  const railButtons = [];
  for (const [index, section] of sections.entries()) {
    const head = el('h3', 'pal-section');
    head.dataset.family = section.family;
    head.id = 'pal-section-' + index;
    head.append(el('span', 'pal-dot'), section.name);
    const group = el('section', 'pal-group');
    group.setAttribute('aria-labelledby', head.id);
    group.append(head);
    for (const [module, entries] of section.modules) {
      const sub = el('h4', 'pal-module', moduleTitle(module));
      sub.dataset.module = module;
      if (module && catalog.module_info?.[module]?.support) sub.title = catalog.module_info[module].support;
      group.append(sub);
      for (const sig of entries) {
        const item = miniBlock(sig);
        item.dataset.module = module || 'Operations';
        item.title = sig.typed_signature || sig.name;
        item.setAttribute('aria-pressed', 'false');
        item.addEventListener('click', () => handlers.arm?.(sig, item));
        item.addEventListener('pointerdown', event => handlers.grab?.(sig, event, item));
        item.addEventListener('focus', () => handlers.hover?.(sig));
        item.addEventListener('mouseenter', () => handlers.hover?.(sig));
        items.push({item, sig, sub, group, base: item.title, text: [sig.name, human(sig.name), module, sig.result,
          sig.description, section.name].join(' ').toLowerCase()});
        group.append(item);
      }
    }
    list.append(group);
    const jump = button('', () => {
      search.value = '';
      filter();
      scrollInside(list, head, 'start');
      mark(index);
    }, 'rail-item');
    jump.dataset.family = section.family;
    jump.append(el('span', 'rail-dot'), el('span', 'rail-label', section.short));
    jump.title = section.name;
    jump.setAttribute('aria-label', section.name);
    const count = el('span', 'rail-count');
    count.hidden = true;
    jump.append(count);
    rail.append(jump);
    railButtons.push({jump, head, group, count});
  }
  list.append(empty);

  function mark(index) {
    railButtons.forEach(({jump}, i) => jump.classList.toggle('active', i === index));
  }
  mark(0);
  list.addEventListener('scroll', () => {
    const top = list.getBoundingClientRect().top;
    let current = 0;
    railButtons.forEach(({head}, i) => { if (head.getBoundingClientRect().top - top < 40) current = i; });
    mark(current);
  }, {passive: true});

  function filter() {
    const query = search.value.trim().toLowerCase().replaceAll('_', ' ');
    const words = query.split(/\s+/).filter(Boolean);
    const only = onlyFits && hinted?.fits;
    let shown = 0;
    for (const entry of items) {
      entry.item.hidden = !words.every(word => entry.text.includes(word)) || Boolean(only && !entry.item.dataset.fit);
      if (!entry.item.hidden) shown++;
    }
    for (const sub of list.querySelectorAll('.pal-module')) {
      let next = sub.nextElementSibling;
      let any = false;
      while (next && next.classList.contains('pal-block')) { if (!next.hidden) any = true; next = next.nextElementSibling; }
      sub.hidden = !any;
    }
    for (const group of list.querySelectorAll('.pal-group')) {
      group.hidden = ![...group.querySelectorAll('.pal-block')].some(item => !item.hidden);
    }
    empty.hidden = shown > 0;
    empty.textContent = only && !words.length ? 'No block takes this value.' : 'No block matches this search.';
  }

  let hinted = null;
  let onlyFits = false;
  // A block's entry in the fits, from its own module or another that shares the block.
  const fitOf = (fits, sig) => fits[sig.module || '']?.[sig.name] ||
    Object.values(fits).map(blocks => blocks[sig.name]).find(Boolean);
  function decorate(entry, fit, title) {
    const {item} = entry;
    item.querySelector('.pal-fit')?.remove();
    item.querySelector('.hole-fit')?.classList.remove('hole-fit');
    item.title = entry.base;
    if (!fit) { delete item.dataset.fit; return; }
    item.dataset.fit = fit.via ? 'via' : 'direct';
    const inputs = fit.inputs.map(human).join(' or ');
    item.title = entry.base + '\n' + (fit.via ? 'Takes ' + title + ' through ' + human(fit.via) + ', as its ' + inputs :
      'Takes ' + title + ' as its ' + inputs);
    const hole = !fit.via && [...item.querySelectorAll('.pal-hole')].find(h => fit.inputs.includes(h.dataset.param));
    if (hole) hole.classList.add('hole-fit');
    else item.append(el('span', 'pal-fit', fit.via ? 'via ' + human(fit.via) : 'as ' + human(fit.inputs[0])));
  }
  function caption(state, count) {
    strip.replaceChildren();
    strip.dataset.family = state.family;
    const lead = el('span', 'pal-hint-lead');
    const glyph = keyGlyph(state.family, 'key key-chip');
    if (glyph) lead.append(glyph);
    const name = el('strong', '', state.title);
    if (state.pending) lead.append('Finding blocks that take ', name, '…');
    else if (count) lead.append(plural(count, 'block'), count === 1 ? ' takes ' : ' take ', name);
    else lead.append(state.typed ? 'No block takes ' : 'Fix the problems in ', name, state.typed ? ' yet.' : ' to see what takes it.');
    const close = iconButton('x', 'Stop hinting', () => handlers.clearHint?.(), 'icon-btn pal-hint-close');
    strip.append(lead, close);
    if (count) {
      const only = button(onlyFits ? 'Show all blocks' : 'Show only these', () => {
        onlyFits = !onlyFits;
        only.textContent = onlyFits ? 'Show all blocks' : 'Show only these';
        only.setAttribute('aria-pressed', String(onlyFits));
        filter();
      }, 'pal-hint-only');
      only.setAttribute('aria-pressed', String(onlyFits));
      const note = el('span', 'pal-hint-note', items.some(e => e.item.dataset.fit === 'via') ?
        'Dashed blocks take it through another block.' : '');
      const row = el('span', 'pal-hint-row');
      row.append(only, note);
      strip.append(row);
    }
  }
  function hint(state) {
    const same = hinted && state && hinted.title === state.title && hinted.block === state.block;
    // While Python looks, the hints for the same value stay.
    if (state?.pending && same && hinted.fits) return;
    const shown = same && Boolean(hinted.fits);
    hinted = state;
    panel.classList.toggle('hinting', Boolean(state?.fits));
    strip.hidden = !state;
    if (!state) {
      for (const entry of items) decorate(entry, null);
      for (const {jump, count} of railButtons) { jump.classList.remove('unfit'); count.hidden = true; }
      onlyFits = false;
      filter();
      return;
    }
    let total = 0;
    for (const entry of items) {
      const fit = state.fits && fitOf(state.fits, entry.sig);
      decorate(entry, fit, state.title);
      if (fit) total++;
    }
    for (const {jump, group, count} of railButtons) {
      const n = state.fits ? group.querySelectorAll('.pal-block[data-fit]').length : 0;
      count.textContent = String(n);
      count.hidden = !n;
      jump.classList.toggle('unfit', Boolean(state.fits) && !n);
    }
    for (const sub of list.querySelectorAll('.pal-module')) {
      let next = sub.nextElementSibling;
      let any = false;
      while (next && next.classList.contains('pal-block')) { if (next.dataset.fit) any = true; next = next.nextElementSibling; }
      sub.classList.toggle('has-fit', any);
    }
    caption(state, total);
    filter();
    // Bring a hinted block into view when none shows.
    const fitting = items.filter(e => e.item.dataset.fit && !e.item.hidden).map(e => e.item);
    const view = list.getBoundingClientRect();
    const seen = fitting.some(item => { const box = item.getBoundingClientRect(); return box.top >= view.top && box.bottom <= view.bottom; });
    if (fitting.length && !seen && !shown) scrollInside(list, fitting.find(i => i.dataset.fit === 'direct') || fitting[0], 'center');
  }
  search.addEventListener('input', filter);
  search.addEventListener('keydown', event => {
    if (event.key === 'Enter') {
      const first = items.find(entry => !entry.item.hidden);
      if (first) { event.preventDefault(); first.item.click(); }
    }
    if (event.key === 'Escape') { search.value = ''; filter(); }
  });

  return {
    search,
    hint,
    setArmed(sig) {
      for (const {item, sig: entry} of items) item.setAttribute('aria-pressed', String(entry === sig));
    },
    setImports(imports) {
      for (const sub of list.querySelectorAll('.pal-module')) {
        sub.classList.toggle('in-use', imports.includes(sub.dataset.module));
      }
    },
  };
}
