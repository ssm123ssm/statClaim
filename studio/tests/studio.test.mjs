import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync, readdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';

const { Window } = await import(process.env.STATCLAIM_DOM || 'happy-dom');
const platform = new URL('../', import.meta.url);
const root = new URL('../', platform);
const tutorials = new URL('examples/tutorial/', root);
const python = process.env.STATCLAIM_PYTHON || fileURLToPath(new URL('.venv/bin/python', root));
const fixture = fileURLToPath(new URL('./dispatch.py', import.meta.url));

function dispatch(path, { method = 'GET', body = '' } = {}) {
  const reply = spawnSync(python, [fixture], {
    input: JSON.stringify({ path, method, body }), encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
  });
  assert.equal(reply.status, 0, reply.error?.message || reply.stderr);
  const result = JSON.parse(reply.stdout);
  return new Response(result.body, {status: result.status});
}

async function until(predicate, explanation) {
  const deadline = Date.now() + 5000;
  while (!predicate()) {
    if (Date.now() >= deadline) assert.fail(explanation);
    await new Promise(resolve => setTimeout(resolve, 20));
  }
}

function install(window) {
  for (const key of ['window', 'document', 'HTMLElement', 'HTMLInputElement', 'CSS', 'MutationObserver', 'localStorage', 'Event']) {
    globalThis[key] = key === 'window' ? window : window[key];
  }
}
const shell = () => readFileSync(new URL('index.html', platform), 'utf8')
  .split('<body>')[1].split('</body>')[0].replace(/<script[^>]*>[\s\S]*?<\/script>/g, '');

test('tutorials, live Python diagnostics, undo and workspace isolation', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  const requests = [];
  globalThis.fetch = async (url, options = {}) => {
    const result = dispatch(url, options);
    requests.push({ url, source: options.body && JSON.parse(options.body).source });
    return result;
  };
  // Node imports the real module explicitly. Suppress duplicate script and CSS loads.
  document.body.innerHTML = shell();
  await import(new URL('editor.js', platform));
  const el = id => document.getElementById(id);
  const event = (type, extra = {}) => Object.assign(new window.Event(type, {bubbles: true}), extra);
  const key = (target, name) => target.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true}));
  const picker = el('lesson');
  const src = el('source');
  const host = el('lessonBlocks');
  const names = readdirSync(tutorials).filter(name => name.endsWith('.stat'));
  const read = name => readFileSync(new URL(name, tutorials), 'utf8');
  const open = name => { picker.value = name; picker.dispatchEvent(event('change')); };
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const pop = () => host.querySelector('.pop');
  const label = node => (node.querySelector('.opt-label, .pal-name, .menu-label') || node).textContent;
  const choose = text => {
    const match = [...pop().querySelectorAll('.opt, .menu-item')].find(node => label(node) === text);
    assert.ok(match, 'missing choice ' + text + ' in ' + pop().getAttribute('aria-label'));
    match.click();
  };
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !picker.disabled && Array.from(picker.options).some(o => o.value === names.at(-1)), 'tutorial catalogue never loaded');

  await until(() => host.querySelector('.stack .blk-root'), 'expected blocks on first load');
  assert.ok(document.getElementById('paletteSearch'));
  assert.ok(document.querySelector('.rail-item'));

  // Changing one use of a shared value leaves its other uses alone.
  open('05_several_endpoints.stat');
  await until(() => !host.inert && src.value === read('05_several_endpoints.stat'), 'shared study failed');
  stack('remission').querySelector('[data-slot="null"] .pill').click();
  assert.equal(pop().getAttribute('aria-label'), 'Choose null');
  choose('proportion difference');
  await until(() => !host.inert && src.value.includes('value=choose_value'), 'missing input was not exposed');
  const value = stack('remission').querySelector('[data-slot="value"] input');
  assert.ok(value, 'an empty numeric input should be typed into directly');
  value.value = '1/10';
  value.dispatchEvent(event('change'));
  const isolated = read('05_several_endpoints.stat').replace(
    'let remission = fisher(design=design, null=null',
    'let remission = fisher(design=design, null=proportion_difference(model=study, value=1/10)');
  await until(() => !host.inert && src.value === isolated, 'editing remission also changed another endpoint');
  assert.ok(el('report').querySelector('button'));
  el('restoreLesson').click();
  await until(() => !host.inert && src.value === read('05_several_endpoints.stat'), 'failed to restore');
  assert.deepEqual([...stack('design').querySelectorAll('.use-chip')].map(c => c.textContent), ['response', 'remission', 'relapse']);
  stack('design').querySelector('.blk-root > .blk-head .blk-name').click();
  choose('Replace with another block');
  assert.ok(![...pop().querySelectorAll('.opt-block .pal-name')].some(n => n.textContent === 'fisher'), 'only designs should replace a design');
  choose('adaptive');
  await until(() => !host.inert && src.value === read('05_several_endpoints.stat').replace('fixed(model=study)', 'adaptive(model=study)'), 'shared design replacement lost model or uses');
  el('undo').click();
  await until(() => !host.inert && src.value === read('05_several_endpoints.stat'), 'failed to undo shared design edit');

  open('example/two_stage_result.stat');
  await until(() => !host.inert && src.value.includes('two_stage_test'), 'two-stage study failed');
  const rate = host.querySelector('input[aria-label="null rate"]');
  assert.equal(rate.value, '1/5');
  rate.value = '1/4';
  rate.dispatchEvent(event('change'));
  await until(() => !host.inert && src.value.includes('null_rate=1/4'), 'editing a scalar input failed');
  for (const name of names) {
    open(name);
    await until(() => !host.inert && src.value === read(name) && host.querySelector('.stack'), 'tutorial failed to render: ' + name);
  }

  const shared = '05_several_endpoints.stat';
  open(shared);
  await until(() => src.value === read(shared), 'shared study did not load');
  const changed = read(shared).replace('n_control=50', 'n_control=48');
  src.value = changed;
  src.dispatchEvent(event('input'));
  await until(() => requests.some(r => r.url === '/api/compile' && r.source === changed), 'source changes should compile without pressing Recheck');
  el('undo').click();
  await until(() => src.value === read(shared), 'Undo did not restore original source');
  el('redo').click();
  await until(() => src.value === changed, 'Redo did not restore edit');
  const broken = '06_changed_levels.stat';
  open(broken);
  await until(() => !host.inert && src.value === read(broken) && host.querySelector('.stack'), 'changed-levels study did not load');
  const diagnostics = (await dispatch('/api/compile', { method: 'POST', body: JSON.stringify({source: read(broken)}) }).json()).diagnostics;
  assert.ok(diagnostics.length);
  await until(() => el('report').textContent.includes(diagnostics[0].code), 'compiler diagnostic missing from report');
  assert.match(el('statusText').textContent, /open obligation/);
  open(shared);
  await until(() => src.value === changed, 'switching tutorials lost a study edit');
  el('restoreLesson').click();
  await until(() => src.value === read(shared), 'Restore original did not reset the study');
  await ready();

  // Typing a value previews it with Python before it is kept.
  const alpha = stack('response').querySelector('input[aria-label="alpha"]');
  assert.equal(alpha.value, '1/40');
  alpha.focus();
  alpha.value = 'x';
  alpha.dispatchEvent(event('input'));
  assert.equal(alpha.getAttribute('aria-invalid'), 'true');
  assert.ok(host.querySelector('.bubble-error'), 'an invalid number should explain itself');
  alpha.value = '2';
  alpha.dispatchEvent(event('input'));
  await until(() => el('report').dataset.state === 'error', 'invalid uncommitted level did not show live feedback');
  assert.equal(src.value, read(shared));
  alpha.value = '1/80';
  alpha.dispatchEvent(event('change'));
  await ready();
  assert.equal(src.value, read(shared).replace('alpha=1/40', 'alpha=1/80'));

  // A new study, built from the add bar, the "use in" menu and an inline rename. New offers a wizard first.
  el('newDoc').click();
  assert.ok(document.querySelector('.wizard'));
  [...document.querySelectorAll('.wizard button')].find(b => b.textContent === 'Start empty').click();
  await ready();
  assert.ok(host.querySelector('.starter'));
  document.querySelector('.add-main').click();
  choose('two arm binomial');
  await ready();
  assert.match(src.value, /^use models.two_arm_binomial\nlet study = two_arm_binomial\(/);
  assert.equal(el('report').dataset.state, 'ready');
  stack('study').querySelector('.use-next').click();
  choose('fixed · model');
  await ready();
  assert.match(src.value, /let design = fixed\(model=study\)/);
  assert.equal(el('report').dataset.state, 'ready');
  stack('study').querySelector('.stack-name').click();
  const rename = host.querySelector('.rename-input');
  rename.value = 'design';
  rename.dispatchEvent(event('input'));
  assert.equal(rename.getAttribute('aria-invalid'), 'true', 'a duplicate name should be refused');
  rename.value = 'trial';
  rename.dispatchEvent(event('input'));
  key(rename, 'Enter');
  await ready();
  assert.match(src.value, /let design = fixed\(model=trial\)/);
  assert.match(src.value, /let trial = two_arm_binomial\(/);

  // The Fisher block exposes two different typed openings.
  open('01_first_claim.stat');
  await ready();
  const pointer = (target, type, x, y, extra = {}) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: y, pointerId: 1, ...extra}));
  const lift = node => { pointer(node, 'pointerdown', 0, 0); pointer(document, 'pointermove', 30, 30); };
  const dropOn = (onto, extra) => { document.elementFromPoint = () => onto; pointer(document, 'pointerup', 30, 30, extra); };
  const design = stack('design').querySelector('.stack-name');
  lift(design);
  assert.ok(document.querySelector('.drag-avatar'), 'a dragged value follows the pointer as a block');
  assert.equal(stack('analysis').querySelector('[data-slot="design"]').dataset.active, 'true');
  assert.equal(stack('analysis').querySelector('[data-slot="null"]').dataset.active, undefined);
  dropOn(document.body);
  assert.equal(stack('analysis').querySelector('[data-slot="design"]').dataset.active, undefined, 'a drop on nothing cancels');
  // Emptying an input reads as a gap to fill, not an unknown name.
  key(stack('analysis').querySelector('[data-slot="null"] .pill'), 'Delete');
  await ready();
  assert.match(src.value, /null=choose_null/);
  assert.match(el('report').textContent, /Empty input/);
  assert.match(el('report').textContent, /The null input is empty/);
  el('undo').click();
  await ready();
  stack('analysis').querySelector('[data-slot="null"] .pill').click();
  assert.ok(pop());

  // Arming a palette block lights only the inputs it fits.
  const paletteBlock = name => [...document.querySelectorAll('#library .pal-block')].find(b => b.querySelector('.pal-name').textContent === name);
  paletteBlock('equal proportions').click();
  assert.ok(document.querySelector('#overlay .place-banner'));
  assert.equal(stack('analysis').querySelector('[data-slot="null"]').dataset.active, 'true');
  assert.equal(stack('analysis').querySelector('[data-slot="design"]').dataset.active, undefined);
  key(document, 'Escape');
  assert.ok(!document.querySelector('.place-banner'));

  open(shared);
  await ready();
  stack('endpoints').querySelector('[aria-label="Move item 2 earlier"]').click();
  await ready();
  assert.ok(src.value.includes('analyses=[remission, response, relapse]'));
  stack('endpoints').querySelector('[aria-label="Remove joint law"]').click();
  await ready();
  assert.ok(!src.value.includes('joint_law='));
  assert.equal(el('report').dataset.state, 'ready');
  el('undo').click();
  await ready();
  el('undo').click();
  await ready();
  const analysisHandle = stack('remission').querySelector('.stack-name');
  lift(analysisHandle);
  const firstMember = stack('endpoints').querySelector('[data-slot="item 1"]');
  assert.equal(firstMember.dataset.active, 'true');
  dropOn(firstMember);
  await ready();
  assert.ok(src.value.includes('analyses=[remission, remission, relapse]'));
  el('undo').click();
  await ready();

  open('13_mixed_endpoints.stat');
  await ready();
  const nested = [...stack('response').querySelectorAll('.blk-call:not(.blk-root)')].find(
    block => block.querySelector(':scope > .blk-head .blk-name').textContent === 'fixed');
  assert.ok(nested);
  nested.querySelector('.blk-name').click();
  choose('Make it a shared value');
  await ready();
  assert.match(src.value, /let design = fixed\(model=responders\)\nlet response/);
  assert.match(src.value, /design=design,/);
  assert.equal(el('report').dataset.state, 'ready');

  open('06_changed_levels.stat');
  await ready();
  assert.ok(host.querySelector('.has-issue .issue-badge, .issue-badge'));
  host.querySelector('.issue-badge').click();
  assert.ok(pop().classList.contains('issue-pop'));
  key(pop(), 'Escape');
  el('report').querySelector('button').click();
  assert.ok(host.contains(document.activeElement));
  open(shared);
  await ready();
  assert.equal(src.value, read(shared).replace('alpha=1/40', 'alpha=1/80'));

  // Notes are # comments directly above a value.
  stack('response').querySelector('.hat-btn').click();
  choose('Add note');
  const note = pop().querySelector('textarea');
  note.value = 'Primary endpoint';
  pop().querySelector('form').dispatchEvent(event('submit'));
  await ready();
  assert.match(src.value, /\n# Primary endpoint\nlet response = /);
  assert.equal(stack('response').querySelector('.stack-note-text').textContent, 'Primary endpoint');
  el('undo').click();
  await ready();

  // Recreate the shell as a tab reload would, retaining session storage.
  document.body.innerHTML = shell();
  await import(new URL('editor.js?reload', platform));
  await until(() => el('report').dataset.state === 'ready', 'restored study failed to compile');
  assert.equal(el('lesson').value, shared);
  assert.equal(el('source').value, read(shared).replace('alpha=1/40', 'alpha=1/80'));
  assert.ok([...el('lesson').options].some(o => o.value.startsWith('local/')));
  const originalFetch = globalThis.fetch;
  let release;
  const stale = 'let obsolete = unbound_name\n';
  globalThis.fetch = async (url, options = {}) => {
    const response = await originalFetch(url, options);
    if (url === '/api/compile' && JSON.parse(options.body).source === stale) {
      await new Promise(resolve => { release = resolve; });
    }
    return response;
  };
  el('source').value = stale;
  el('source').dispatchEvent(event('input'));
  await until(() => release, 'older compiler response never started');
  el('source').value = 'let fresh = 2\n';
  el('source').dispatchEvent(event('input'));
  await until(() => el('report').dataset.state === 'ready', 'new revision did not compile');
  release();
  await new Promise(resolve => setTimeout(resolve, 20));
  assert.equal(el('report').dataset.state, 'ready');
  assert.equal(el('lessonBlocks').querySelector('.stack-name').textContent, 'fresh');
  globalThis.fetch = originalFetch;
  const file = el('openFile');
  const imported = '# 🌍 exact lines\r\nlet value = ["a", 1/3]\r\n';
  Object.defineProperty(file, 'files', {value: [{name: 'my-study.stat', text: async () => imported}]});
  file.dispatchEvent(event('change'));
  await until(() => el('filename').textContent === 'my-study.stat' && el('report').dataset.state === 'ready', 'file import failed');
  const anchorClick = window.HTMLAnchorElement.prototype.click;
  let saved;
  window.HTMLAnchorElement.prototype.click = function () { saved = {url: this.href, name: this.download}; };
  try {
    el('download').click();
    assert.equal(saved.name, 'my-study.stat');
    const blob = await (await import('node:buffer')).resolveObjectURL(saved.url).text();
    assert.equal(blob, imported);
  } finally { window.HTMLAnchorElement.prototype.click = anchorClick; }
});

test('every registered constructor can be authored and every example expression has a block', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const host = document.createElement('main');
  document.body.append(host);
  let next;
  const generated = [];
  const signatures = Object.assign({}, ...Object.values(manifest.modules), manifest.operations);
  for (const [name, signature] of Object.entries(signatures)) {
    mountDocument(host, {...manifest, source: '', onChange: s => { next = s; }});
    host.querySelector('.add-main').click();
    const choice = [...host.querySelectorAll('.pop .opt-block')].find(b => b.querySelector('.pal-name').textContent === name.replaceAll('_', ' '));
    assert.ok(choice, name);
    next = undefined;
    choice.click();
    assert.ok(next.includes(' = ' + name + '('), next);
    if (!manifest.operations[name]) assert.ok(next.startsWith('use '), name);
    for (const param of Object.keys(signature.parameters)) {
      if (!signature.optional.includes(param)) assert.ok(next.includes(param + '='));
    }
    generated.push(next);
  }
  const parsed = await dispatch('/api/parse', {method: 'POST', body: JSON.stringify({source: generated.join('\n')})}).json();
  assert.deepEqual(parsed.parse_errors, []);
  assert.equal(parsed.statements.length, generated.length);
  mountDocument(host, {...manifest, ...parsed, onChange: () => assert.fail('opening an editor changed source')});
  const stacks = [...host.querySelectorAll('.stack')];
  assert.equal(stacks.length, parsed.statements.length);
  for (const [i, card] of stacks.entries()) {
    const name = parsed.statements[i].expression.label;
    for (const param of Object.keys(signatures[name].parameters)) {
      const label = param.replaceAll('_', ' ');
      const found = signatures[name].optional.includes(param) ?
        card.querySelector('[aria-label="Add ' + label + '"]') : card.querySelector('.blk-root > .params [data-slot="' + label + '"]');
      assert.ok(found, name + '.' + param);
    }
    card.querySelector('.blk-root > .blk-head .blk-name').click();
    assert.equal(host.querySelector('.pop').getAttribute('aria-label'), name.replaceAll('_', ' '));
  }
  for (const endpoint of ['examples', 'tutorials']) {
    for (const doc of await dispatch('/api/' + endpoint).json()) {
      mountDocument(host, {...manifest, ...doc, onChange: () => assert.fail('render changed source')});
      const nodes = host.querySelectorAll('.blk');
      const count = node => 1 + (node.children || []).reduce((sum, n) => sum + count(n), 0);
      assert.equal(nodes.length, doc.statements.reduce((sum, s) => sum + count(s.expression), 0), doc.name);
    }
  }
});

test('stack menu reorders, duplicates and deletes without breaking references', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const doc = (await dispatch('/api/tutorials').json()).find(d => d.name === '01_first_claim.stat');
  const host = document.createElement('main');
  document.body.append(host);
  let next;
  const mount = () => mountDocument(host, {...manifest, ...doc, onChange: s => { next = s; }});
  const menu = (name, text) => {
    mount();
    host.querySelector('.stack[data-name="' + name + '"] .hat-btn').click();
    return [...host.querySelectorAll('.pop .menu-item')].find(b => b.querySelector('.menu-label').textContent === text);
  };
  assert.equal(menu('analysis', 'Move earlier in file').disabled, true, 'analysis uses null, so it cannot move above it');
  assert.equal(menu('study', 'Delete').disabled, true, 'a used value cannot be deleted');
  menu('null', 'Move earlier in file').click();
  assert.ok(next.includes('let null = equal_proportions(model=study)\nlet design = fixed(model=study)\n'));
  menu('design', 'Duplicate').click();
  assert.ok(next.includes('let design = fixed(model=study)\nlet design_2 = fixed(model=study)\n'));
  menu('verification', 'Delete').click();
  assert.ok(!next.includes('verify('));
  assert.ok(next.endsWith('let claim = typeI(analysis)\n'));
});

test('stacks move freely, keep their places and offer right-click menus', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const doc = (await dispatch('/api/tutorials').json()).find(d => d.name === '01_first_claim.stat');
  const host = document.createElement('main');
  document.body.append(host);
  let saved = 'unset';
  let next;
  const mount = layout => mountDocument(host, {...manifest, ...doc, layout, onLayout: map => { saved = map; }, onChange: s => { next = s; }});
  const card = name => host.querySelector('.stack[data-name="' + name + '"]');
  const key = (target, name, extra = {}) => target.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true, ...extra}));
  const pointer = (target, type, x, y) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: y}));

  mountDocument(host, {...manifest, source: 'use models.two_arm_binomial\nlet m = two_arm_binomial(n_control=1, n_treatment=1, better="higher")\n',
    ...(await dispatch('/api/parse', {method: 'POST', body: JSON.stringify({source: 'use models.two_arm_binomial\nlet m = two_arm_binomial(n_control=1, n_treatment=1, better="higher")\n'})}).json()),
    onChange: () => {}});
  const better = host.querySelector('select[aria-label="better"]');
  assert.deepEqual([...better.options].map(o => o.value), ['higher', 'lower'], 'fixed string values become a dropdown');

  mount(null);
  key(card('verification'), 'Delete');
  assert.ok(!next.includes('verify('), 'Delete removes an unused stack');
  next = undefined;
  mount(null);
  const left = parseFloat(card('study').style.left);
  const top = parseFloat(card('study').style.top);
  pointer(card('study').querySelector('.hat-kw'), 'pointerdown', 0, 0);
  pointer(document, 'pointermove', 120, 60);
  assert.ok(card('study').classList.contains('moving'));
  pointer(document, 'pointerup', 120, 60);
  assert.deepEqual(saved.study, [left + 120, top + 60], 'a moved stack keeps its new place');
  assert.ok(Object.keys(saved).includes('verification'), 'moving one stack pins the others where they are');
  assert.equal(next, undefined, 'moving a stack never edits the source');

  // A small wobble is a click, not a move.
  saved = 'unset';
  pointer(card('design').querySelector('.hat-kw'), 'pointerdown', 0, 0);
  pointer(document, 'pointerup', 2, 1);
  assert.equal(saved, 'unset');

  mount({study: [400, 300]});
  assert.equal(card('study').style.left, '400px');
  assert.equal(card('study').style.top, '300px');

  card('analysis').querySelector('.hat').dispatchEvent(new window.MouseEvent('contextmenu', {bubbles: true, clientX: 5, clientY: 5}));
  assert.equal(host.querySelector('.pop').getAttribute('aria-label'), 'analysis');
  card('analysis').querySelector('[data-slot="design"] .pill').dispatchEvent(new window.MouseEvent('contextmenu', {bubbles: true, clientX: 5, clientY: 5}));
  assert.equal(host.querySelector('.pop').getAttribute('aria-label'), 'Choose design');
  host.querySelector('.board').dispatchEvent(new window.MouseEvent('contextmenu', {bubbles: true, clientX: 5, clientY: 5}));
  const canvasMenu = host.querySelector('.pop');
  assert.equal(canvasMenu.getAttribute('aria-label'), 'Canvas');
  [...canvasMenu.querySelectorAll('.menu-item')].find(b => b.textContent.startsWith('Clean up blocks')).click();
  assert.equal(saved, null, 'clean up returns to the file-order column');

  // Arrange by flow: each value sits one column right of what it uses.
  host.querySelector('.board').dispatchEvent(new window.MouseEvent('contextmenu', {bubbles: true, clientX: 5, clientY: 5}));
  [...host.querySelectorAll('.pop .menu-item')].find(b => b.textContent.startsWith('Arrange by flow')).click();
  const column = name => saved[name][0];
  assert.ok(column('study') < column('design') && column('design') === column('null') && column('null') < column('analysis'));
  assert.ok(column('analysis') < column('claim') && column('claim') < column('verification'));

  // A level reads as a percentage; a whole number steps with − and +.
  mount(null);
  assert.equal(card('analysis').querySelector('[data-slot="alpha"] .lit-percent').textContent, '= 5%');
  next = undefined;
  card('study').querySelector('[aria-label="Increase n control"]').click();
  assert.match(next, /two_arm_binomial\(n_control=51, n_treatment=50\)/);
});

test('runs checks, suggests contract fixes, and offers commands, keys and code completion', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  let runs = 0;
  const canned = {
    status: 'verified', run_directory: '/tmp/run', certificate_issued: true, diagnostics: [],
    requests: [{
      request_id: 1, operation: 'verify', claim: 'typeI', subject: 'analysis', name: 'verification', status: 'verified',
      source: {line: 12, column: 20, end_line: 12, end_column: 32},
      weakest_link: {grade: 'proved', parts: ['the claim']},
      evidence: {grade: 'proved', scope: 'finite_sample', guarantee: {quantity: 'type_I_error', bound: '1/20'},
        assumptions: [{id: 'fixed', kind: 'design', text: 'Arm sizes were fixed in advance.', status: 'declared'}]},
      established: ['The Fisher analysis has Type I error at most 1/20.'], assumptions: [], references: [],
      certificate: '/tmp/run/request-001', calculation: null, decision: null, message: null,
    }],
  };
  globalThis.fetch = async (url, options = {}) => {
    if (url === '/api/run') { runs++; return new Response(JSON.stringify(canned)); }
    return dispatch(url, options);
  };
  document.body.innerHTML = shell();
  await import(new URL('editor.js?features', platform));
  const el = id => document.getElementById(id);
  const event = type => new window.Event(type, {bubbles: true});
  const key = (target, name, extra = {}) => target.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true, ...extra}));
  const host = el('lessonBlocks');
  const src = el('source');
  const picker = el('lesson');
  const read = name => readFileSync(new URL(name, tutorials), 'utf8');
  const open = name => { picker.value = name; picker.dispatchEvent(event('change')); };
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  await until(() => !picker.disabled && host.querySelector('.stack'), 'editor never loaded');
  open('01_first_claim.stat');
  await until(() => src.value === read('01_first_claim.stat'), 'lesson 1 did not open');
  await ready();

  // Running shows each claim's grade on its block and in the Results tab.
  assert.equal(el('runChecks').disabled, false);
  assert.match(stack('verification').querySelector('.result-tray').textContent, /Run check/);
  el('runChecks').click();
  await until(() => host.querySelector('.result-tray[data-state="done"]'), 'run results never appeared');
  assert.equal(runs, 1);
  assert.match(stack('verification').querySelector('.result-tray').textContent, /Proved in Lean.*finite-sample bound/i);
  // The grade and its links sit on one row; what was found has a full-width row of its own.
  const done = stack('verification').querySelector('.result-tray');
  assert.ok(done.querySelector('.result-top .outcome') && done.querySelector('.result-top .tray-links'));
  assert.equal(done.querySelector('.tray-headline').textContent, 'Type I error at most 1/20');
  assert.equal(done.querySelector('.result-top').contains(done.querySelector('.tray-headline')), false);
  // Lean certified it, so the block wears a medal that lands once, and the Results entry a small one.
  const stamp = stack('verification').querySelector('.cert-stamp');
  assert.ok(stamp && stamp.classList.contains('landing'));
  assert.match(stamp.getAttribute('aria-label'), /Certified in Lean/);
  assert.equal(host.querySelectorAll('.cert-stamp').length, 1, 'only the certified check');
  assert.ok(el('results').querySelector('.entry-hat .entry-medal'));
  assert.equal(el('panel-results').hidden, false);
  assert.match(el('results').textContent, /Type I error at most 1\/20/);
  assert.match(el('results').textContent, /1 assumption/);
  // Each result wears its block's hat, named as on the canvas.
  const entry = el('results').querySelector('.result-entry');
  assert.equal(entry.querySelector('.entry-hat .entry-name').textContent, 'verification');
  assert.equal(entry.querySelector('.entry-hat').dataset.family, 'run');
  assert.ok(entry.querySelector('.entry-panel .entry-headline'));
  const size = stack('study').querySelector('input[aria-label="n control"]');
  size.value = '60';
  size.dispatchEvent(event('change'));
  await ready();
  assert.equal(stack('verification').querySelector('.result-tray').dataset.stale, 'true', 'an edit makes results outdated');
  assert.equal(stack('verification').querySelector('.cert-stamp').dataset.stale, 'true', 'the medal fades after an edit');
  assert.equal(stack('verification').querySelector('.cert-stamp').classList.contains('landing'), false);
  assert.match(el('results').textContent, /changed after this run/);
  el('undo').click();
  await ready();
  assert.equal(stack('verification').querySelector('.result-tray').dataset.stale, undefined);
  assert.equal(stack('verification').querySelector('.cert-stamp').classList.contains('landing'), false, 'a redraw does not stamp it again');

  // Keyboard: Option+arrow moves a stack; Undo puts it back.
  const before = stack('design').style.left;
  stack('design').focus();
  key(stack('design'), 'ArrowRight', {altKey: true});
  assert.equal(parseFloat(stack('design').style.left), parseFloat(before) + 20);
  el('undo').click();
  await until(() => stack('design').style.left === before, 'undo did not move the stack back');
  stack('design').focus();
  key(stack('design'), 'ArrowDown');
  assert.equal(document.activeElement, stack('null'));

  // The command palette finds values, blocks and actions.
  key(document, 'k', {metaKey: true});
  const palette = document.querySelector('.cmdk');
  assert.ok(palette);
  const query = palette.querySelector('input');
  query.value = 'claim';
  query.dispatchEvent(event('input'));
  assert.equal(palette.querySelector('.cmdk-item[aria-selected="true"] .cmdk-label').textContent, 'claim');
  key(query, 'Enter');
  assert.ok(!document.querySelector('.cmdk'));
  assert.equal(document.activeElement, stack('claim'));

  // Code completion comes from the language server.
  src.focus();
  src.value = read('01_first_claim.stat') + 'let z = fi';
  src.setSelectionRange(src.value.length, src.value.length);
  src.dispatchEvent(event('input'));
  await until(() => document.querySelector('.complete'), 'no completion appeared');
  assert.ok([...document.querySelectorAll('.complete-label')].some(n => n.textContent === 'fisher'));
  key(src, 'Enter');
  assert.ok(src.value.endsWith('let z = ' + document.querySelector('.complete-label')?.textContent) || /let z = f\w+$/.test(src.value));
  el('restoreLesson').click();
  await ready();

  // A null the analysis does not support offers analyses that do, never a different null.
  open('03_wrong_null.stat');
  await until(() => src.value === read('03_wrong_null.stat'), 'lesson 3 did not open');
  await ready();
  // No analysis supports a point difference, so the only offer is a declared test, marked as the weakest.
  await until(() => el('report').querySelector('.fix-option'), 'lesson 3 offered no fix');
  assert.deepEqual([...el('report').querySelectorAll('.fix-label')].map(n => n.textContent), ['Declare your own testdeclared']);
  src.value = read('03_wrong_null.stat').replace('proportion_difference(model=study, value=1/10)', 'proportion_difference_at_most(model=study, value=1/10)');
  src.dispatchEvent(event('input'));
  await until(() => el('report').textContent.includes('Use fisher one sided'), 'no supported analysis was suggested');
  const fixes = [...el('report').querySelectorAll('.fix-option')].map(b => b.querySelector('.fix-label').textContent);
  assert.ok(fixes.some(text => text.includes('Use fisher one sided')), fixes.join(' | '));
  assert.ok(fixes.some(text => text.includes('Use logistic regression one sided') && text.includes('cited')));
  [...el('report').querySelectorAll('.fix-option')].find(b => b.textContent.includes('difference test')).click();
  await ready();
  assert.match(src.value, /let analysis = difference_test\(design=design, null=null, alpha=1\/20\)/);
  assert.ok(src.value.startsWith('# Lesson 3a'), 'the opening comment stays first');
  assert.match(src.value, /use tests.fisher\nuse tests.difference\n/);
  assert.equal(el('report').dataset.state, 'ready');
});

test('values move out of inputs by dragging, and inputs can be emptied', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const post = (path, source) => dispatch(path, {method: 'POST', body: JSON.stringify({source})}).json();
  const host = document.createElement('main');
  const trash = document.createElement('aside');
  document.body.append(trash, host);
  let next;
  let saved;
  let toast;
  const mount = async source => mountDocument(host, {...manifest, ...(await post('/api/parse', source)), source,
    bindings: (await post('/api/compile', source)).bindings, trash, layout: null,
    onChange: s => { next = s; }, onLayout: map => { saved = map; }, onToast: message => { toast = message; }});
  const pointer = (target, type, x, y, extra = {}) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: y, pointerId: 1, ...extra}));
  const lift = node => { pointer(node, 'pointerdown', 0, 0); pointer(document, 'pointermove', 30, 30); };
  const over = (onto, extra = {}) => { document.elementFromPoint = () => onto; pointer(document, 'pointermove', extra.clientX ?? 40, extra.clientY ?? 40, extra); };
  const release = (onto, extra = {}) => { document.elementFromPoint = () => onto; pointer(document, 'pointerup', extra.clientX ?? 40, extra.clientY ?? 40, extra); };
  const key = (target, name) => target.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true}));
  const card = name => host.querySelector('.stack[data-name="' + name + '"]');
  const handle = slot => slot.querySelector(':scope > .blk > .blk-head > .blk-name');
  const model = (n, m) => 'two_arm_continuous(n_control=' + n + ', n_treatment=' + m + ')';
  const inline = 'use models.two_arm_continuous\nuse sampling\nuse tests.t\n\n# The two-sided test.\n' +
    'let analysis = t_test(design=fixed(model=' + model(50, 50) + '), null=equal_means(model=' + model(60, 60) + '), alpha=0.05)\n' +
    'let checked = verify(typeI(analysis))\n';
  const nullModel = () => card('analysis').querySelector('[data-slot="null"] [data-slot="model"]');
  const designModel = () => card('analysis').querySelector('[data-slot="design"] [data-slot="model"]');

  // Onto the palette: the value is removed and its required input left empty.
  await mount(inline);
  lift(handle(nullModel()));
  assert.ok(host.querySelector('.drag-hint'), 'dragging out explains where it can go');
  over(trash);
  assert.ok(trash.classList.contains('trash-over'));
  release(trash);
  assert.ok(next.includes('null=equal_means(model=choose_model)'), next);
  assert.ok(!host.querySelector('.drag-hint'));
  const empty = await post('/api/compile', next);
  assert.equal(empty.diagnostics[0].code, 'unknown_name');

  // Into another input: it moves, and its old input is left empty.
  await mount(inline);
  lift(handle(designModel()));
  assert.equal(nullModel().dataset.active, 'true');
  assert.equal(designModel().dataset.active, undefined, 'its own input is not a target');
  release(nullModel());
  assert.ok(next.includes('design=fixed(model=choose_model), null=equal_means(model=' + model(50, 50) + ')'), next);
  assert.match(toast, /Moved two arm continuous to model/);

  // With ⌥ it is copied instead.
  await mount(inline);
  lift(handle(designModel()));
  release(nullModel(), {altKey: true});
  assert.ok(next.includes('design=fixed(model=' + model(50, 50) + '), null=equal_means(model=' + model(50, 50) + ')'), next);

  // Onto empty canvas: it becomes a value of its own, declared above its statement and its note.
  await mount(inline);
  lift(handle(nullModel()));
  over(host.querySelector('.board'), {clientX: 300, clientY: 200});
  assert.ok(host.classList.contains('drop-canvas'));
  release(host.querySelector('.board'), {clientX: 300, clientY: 200});
  assert.ok(next.includes('let study = ' + model(60, 60) + '\n# The two-sided test.\nlet analysis = t_test(design=fixed(model=' + model(50, 50) + '), null=equal_means(model=choose_model)'), next);
  assert.ok(saved.study, 'the new value stays where it was dropped');
  const out = await post('/api/compile', next.replace('choose_model', 'study'));
  assert.deepEqual(out.diagnostics.map(d => d.code), (await post('/api/compile', inline)).diagnostics.map(d => d.code), 'the new value is in scope for the input it left');

  // A named value moves between inputs too; a stack's own name is still a copy.
  const named = 'use models.two_arm_continuous\nuse sampling\nlet study = ' + model(50, 50) + '\nlet other = ' + model(60, 60) +
    '\nlet plan = fixed(model=study)\nlet null = equal_means(model=other)\n';
  await mount(named);
  const pill = () => card('null').querySelector('[data-slot="model"] .pill');
  lift(pill());
  assert.equal(card('null').querySelector('[data-slot="model"]').dataset.active, undefined);
  release(card('plan').querySelector('[data-slot="model"]'));
  assert.ok(next.includes('let plan = fixed(model=other)\nlet null = equal_means(model=choose_model)'), next);
  await mount(named);
  lift(card('other').querySelector('.stack-name'));
  release(card('plan').querySelector('[data-slot="model"]'));
  assert.ok(next.includes('let plan = fixed(model=other)\nlet null = equal_means(model=other)'), next);

  // Delete, the block menu and the chooser empty an input in place.
  await mount(named);
  key(pill(), 'Delete');
  assert.ok(next.includes('let null = equal_means(model=choose_model)'));
  assert.ok(card('null'), 'Delete on a value empties its input, not the whole stack');
  await mount(named);
  pill().click();
  const clear = [...host.querySelectorAll('.pop .opt-clear')];
  assert.equal(clear.length, 1);
  assert.equal(clear[0].querySelector('.opt-label').textContent, 'Empty this input');
  next = undefined;
  clear[0].click();
  assert.ok(next.includes('equal_means(model=choose_model)'));
  await mount(inline);
  handle(nullModel()).click();
  const menu = [...host.querySelectorAll('.pop .menu-item')].find(item => item.textContent.startsWith('Empty this input'));
  assert.ok(menu, 'a nested block menu can empty its input');

  // An empty input draws as a gap and has no way to be emptied again.
  await mount(named.replace('equal_means(model=other)', 'equal_means(model=choose_model)'));
  assert.ok(card('null').querySelector('[data-slot="model"] .pill-hole'));
  card('null').querySelector('[data-slot="model"] .pill-hole').click();
  assert.equal(host.querySelectorAll('.pop .opt-clear').length, 0);
});

test('connector shapes show what fits, and dragged values snap to the nearest input that takes them', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const {miniBlock} = await import(new URL('palette.js', platform));
  const {familyOf, SHAPES} = await import(new URL('ui.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const post = (path, source) => dispatch(path, {method: 'POST', body: JSON.stringify({source})}).json();
  const host = document.createElement('main');
  const trash = document.createElement('aside');
  document.body.append(trash, host);
  let next;
  const source = 'use models.two_arm_binomial\nuse sampling\nuse tests.fisher\n' +
    'let study = two_arm_binomial(n_control=50, n_treatment=50)\nlet other = two_arm_binomial(n_control=60, n_treatment=60)\n' +
    'let design = fixed(model=study)\nlet blank = equal_proportions(model=choose_model)\n' +
    'let analysis = fisher(design=design, null=equal_proportions(model=study), alpha=1/20)\n';
  mountDocument(host, {...manifest, ...(await post('/api/parse', source)), source, bindings: (await post('/api/compile', source)).bindings,
    trash, layout: null, onChange: s => { next = s; }});
  const card = name => host.querySelector('.stack[data-name="' + name + '"]');
  const shape = node => node?.getAttribute('data-shape');
  const pointer = (target, type, x, y, extra = {}) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: y, pointerId: 1, ...extra}));
  const move = (onto, x, y) => { document.elementFromPoint = () => onto; pointer(document, 'pointermove', x, y); };

  // Every kind of value has its own connector, on values, nested blocks, names and empty inputs.
  assert.equal(new Set(Object.values(SHAPES)).size, Object.keys(SHAPES).length);
  assert.equal(shape(card('design').querySelector('[data-slot="model"] > .blk-ref > .key')), 'study');
  assert.equal(shape(card('analysis').querySelector('[data-slot="null"] > .blk-call > .key')), 'null');
  assert.equal(shape(card('analysis').querySelector('[data-slot="design"] > .blk-ref > .key')), 'design');
  assert.equal(shape(card('study').querySelector('.stack-name > .key')), 'study');
  assert.equal(shape(card('blank').querySelector('[data-slot="model"] .key-ghost')), 'study', 'an empty input shows the connector it takes');
  assert.equal(card('analysis').querySelector('.blk-root > .key'), null, 'a stack body has no connector');
  assert.equal(card('analysis').querySelector('[data-slot="alpha"] .key'), null, 'numbers are plain ovals');
  const fisher = miniBlock(manifest.modules['tests.fisher'].fisher);
  assert.equal(shape(fisher.querySelector(':scope > .key')), 'analysis');
  assert.deepEqual([...fisher.querySelectorAll('.pal-hole .key-chip')].map(shape), ['design', 'null'], 'palette blocks show the connectors they take');
  assert.equal(familyOf('Sequential'), 'analysis', 'claims take a group-sequential design where they take an analysis');

  // Near a fitting input, a dragged value snaps to it and shows itself there.
  const target = card('blank').querySelector('[data-slot="model"]');
  target.getBoundingClientRect = () => ({left: 100, right: 160, top: 100, bottom: 126, width: 60, height: 26});
  const board = host.querySelector('.board');
  pointer(card('other').querySelector('.stack-name'), 'pointerdown', 0, 0);
  move(board, 600, 600);
  assert.equal(target.dataset.active, 'true');
  move(board, 180, 140);
  assert.equal(target.dataset.over, 'true', 'a value snaps to an input within reach');
  assert.equal(target.querySelector('.snap-ghost').textContent, 'other');
  assert.equal(shape(target.querySelector('.snap-ghost > .key')), 'study');
  move(board, 500, 500);
  assert.equal(target.dataset.over, undefined);
  assert.equal(target.querySelector('.snap-ghost'), null);

  // An input that does not take it says why, in terms of connectors.
  move(card('analysis').querySelector('[data-slot="alpha"] input'), 900, 900);
  assert.equal(card('analysis').querySelector('[data-slot="alpha"]').dataset.nope, 'true');
  assert.equal(host.querySelector('.bubble').textContent, 'This input takes a number. other is a study model (round connector).');
  move(board, 180, 140);
  assert.equal(host.querySelector('.bubble'), null);
  pointer(document, 'pointerup', 180, 140);
  assert.ok(next.includes('let blank = equal_proportions(model=other)'), next, 'a drop near an input snaps into it');
  assert.equal(document.querySelector('.drag-avatar'), null);

  // Dropped where nothing takes it, a block flies back and nothing changes.
  next = undefined;
  const nested = card('analysis').querySelector('[data-slot="null"] > .blk-call > .blk-head > .blk-name');
  pointer(nested, 'pointerdown', 0, 0);
  move(card('study').querySelector('.hat'), 900, 900);
  pointer(document, 'pointerup', 900, 900);
  assert.equal(next, undefined);
  assert.ok(document.querySelector('.drag-avatar.flying'));
  // A small wobble is not a drag.
  pointer(nested, 'pointerdown', 0, 0);
  pointer(document, 'pointermove', 2, 1);
  pointer(document, 'pointerup', 2, 1);
  assert.equal(document.querySelectorAll('.drag-avatar:not(.flying)').length, 0);

  // Keyboard: Move to another input, then Tab and Enter. A click straight after a drop is ignored, so wait.
  await new Promise(resolve => setTimeout(resolve, 150));
  nested.click();
  assert.ok([...host.querySelectorAll('.pop .menu-item')].some(item => item.textContent.startsWith('Move to another input')));
  card('analysis').querySelector('[data-slot="null"] [data-slot="model"] .pill').click();
  [...host.querySelectorAll('.pop .opt')].find(item => item.textContent.startsWith('Move study to another input')).click();
  assert.match(host.querySelector('.drag-hint').textContent, /Press Tab/);
  const key = (name, extra = {}) => document.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true, ...extra}));
  key('Tab');
  const chosen = host.querySelector('.slot[data-over]');
  assert.ok(chosen, 'Tab chooses an input that takes the value');
  assert.equal(chosen.closest('.stack').dataset.name, 'design');
  key('Tab');
  assert.equal(host.querySelector('.slot[data-over]').closest('.stack').dataset.name, 'blank');
  key('Enter');
  assert.ok(next.includes('let blank = equal_proportions(model=study)'), next);
  assert.ok(next.includes('null=equal_proportions(model=choose_model)'), next);
});

test('errors lead one at a time, edits keep focus, and studies save to their files', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  document.body.innerHTML = shell();
  await import(new URL('editor.js?errors', platform));
  const el = id => document.getElementById(id);
  const event = type => new window.Event(type, {bubbles: true});
  const key = (name, extra = {}) => document.dispatchEvent(new window.KeyboardEvent('keydown', {key: name, bubbles: true, ...extra}));
  const host = el('lessonBlocks');
  const src = el('source');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const pop = () => host.querySelector('.pop');
  await until(() => !el('lesson').disabled && host.querySelector('.stack'), 'editor never loaded');
  await ready();

  // Two empty inputs: the compiler reports the first and the values that use it; the editor finds both.
  src.value = 'use models.two_arm_binomial\nuse sampling\nuse tests.fisher\n' +
    'let study = two_arm_binomial(n_control=50, n_treatment=50)\nlet design = fixed(model=choose_model)\n' +
    'let analysis = fisher(design=design, null=equal_proportions(model=choose_model), alpha=1/20)\nlet claim = typeI(analysis)\n';
  src.dispatchEvent(event('input'));
  await ready();
  assert.equal(el('statusText').textContent, '2 empty inputs');
  assert.equal(el('problemCount').textContent, '2', 'follow-on errors are not counted as problems');
  assert.equal(el('report').querySelectorAll('.problem').length, 2);
  assert.deepEqual([...el('report').querySelectorAll('.problem-chip')].map(c => c.textContent), ['analysis', 'claim']);
  assert.equal(stack('analysis').querySelector('.hat-waiting').textContent, 'waits for design');
  assert.equal(stack('claim').querySelector('.hat-waiting').textContent, 'waits for design');
  assert.equal(el('runLabel').textContent, 'Fill 2 inputs');
  assert.ok(!el('runChecks').disabled, 'the run button leads to the problems');

  // F8 opens each empty input's chooser in turn; filling one keeps focus on it.
  key('F8');
  assert.equal(pop()?.getAttribute('aria-label'), 'Choose model');
  [...pop().querySelectorAll('.opt')].find(o => o.querySelector('.opt-label')?.textContent === 'study').click();
  await ready();
  assert.match(src.value, /let design = fixed\(model=study\)/);
  assert.equal(document.activeElement, stack('design').querySelector('[data-slot="model"] .pill'), 'focus returns to the filled input');
  assert.equal(el('runLabel').textContent, 'Fill 1 input');
  el('runChecks').click();
  assert.equal(pop()?.getAttribute('aria-label'), 'Choose model');
  [...pop().querySelectorAll('.opt')].find(o => o.querySelector('.opt-label')?.textContent === 'study').click();
  await ready();
  assert.equal(el('report').dataset.state, 'ready');
  assert.equal(el('runLabel').textContent, 'Run checks');

  // Save writes to a file and adopts it; the tutorial keeps its original.
  const tutorial = el('lesson').value;
  let picks = 0;
  const written = [];
  window.showSaveFilePicker = async ({suggestedName}) => {
    picks++;
    assert.equal(suggestedName, tutorial);
    return {name: 'my-trial.stat', createWritable: async () => ({write: async text => written.push(text), close: async () => {}})};
  };
  const saved = src.value;
  key('s', {metaKey: true});
  await until(() => el('filename').textContent === 'my-trial.stat', 'save did not adopt the file');
  assert.deepEqual(written, [saved]);
  assert.ok(el('lesson').value.startsWith('local/'));
  assert.ok(el('dirty').hidden, 'a saved study has no unsaved changes');
  const drafts = JSON.parse(window.localStorage.getItem('statclaim.studio.drafts.v2')).drafts;
  assert.ok(drafts.some(d => d.name === 'my-trial.stat' && d.saved === saved), 'drafts outlive the tab');
  src.value = saved.replace('alpha=1/20', 'alpha=1/40');
  src.dispatchEvent(event('input'));
  await ready();
  assert.equal(el('dirty').textContent, 'unsaved');
  assert.ok(!el('dirty').hidden);
  el('download').click();
  await until(() => written.length === 2, 'second save did not write');
  assert.equal(picks, 1, 'later saves write to the same file without asking');
  assert.ok(el('dirty').hidden);

  // Recent edits are named after what changed, and the gutter marks changes since the save.
  await new Promise(resolve => setTimeout(resolve, 950));
  src.value = src.value.replace('n_control=50', 'n_control=80');
  src.dispatchEvent(event('input'));
  await ready();
  assert.equal(document.querySelectorAll('#gutter .diff-changed').length, 1);
  assert.match(el('changeNote').textContent, /1 line changed from the saved file/);
  el('historyButton').click();
  const items = [...document.querySelectorAll('.history-pop .history-item')];
  assert.equal(items[0].querySelector('.history-label').textContent, 'Line 4: 5 → 8');
  items[0].click();
  await ready();
  assert.match(src.value, /n_control=50/);
});

test('the new-study wizard builds studies that compile, and practice turns a lesson into an exercise', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  const {studySource, available} = await import(new URL('wizard.js', platform));
  const compile = source => dispatch('/api/compile', {method: 'POST', body: JSON.stringify({source})}).json();

  // Every combination the wizard offers compiles, and says what its guarantee rests on.
  for (const outcome of ['binary', 'continuous', 'survival']) {
    for (const better of ['higher', 'lower']) {
      for (const question of ['differ', 'better', 'margin']) {
        if (!available(outcome, better)[question]) continue;
        const made = studySource({outcome, better, question, control: 40, treatment: 60, margin: '1/10', alpha: '1/40'});
        const result = await compile(made.source);
        assert.deepEqual(result.diagnostics.filter(d => d.severity === 'error'), [], outcome + ' ' + better + ' ' + question + '\n' + made.source);
        assert.equal(made.evidence, outcome === 'binary' ? 'proved' : 'cited');
      }
    }
  }
  assert.ok(!available('survival', 'higher').better, 'survival offers only the two-sided test');
  assert.ok(!available('binary', 'lower').margin, 'no one-sided binary test where fewer is better');

  document.body.innerHTML = shell();
  await import(new URL('editor.js?wizard', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const src = el('source');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !el('lesson').disabled && host.querySelector('.stack'), 'editor never loaded');
  await ready();

  // The wizard: a continuous outcome where lower is better, asking for non-inferiority.
  el('newDoc').click();
  const wizard = document.querySelector('.wizard');
  const pick = (name, value) => {
    const input = wizard.querySelector('input[name="' + name + '"][value="' + value + '"]');
    input.checked = true;
    input.dispatchEvent(new window.Event('change', {bubbles: true}));
  };
  const submit = () => wizard.querySelector('form').dispatchEvent(new window.Event('submit', {bubbles: true, cancelable: true}));
  const next = wizard.querySelector('.wizard-foot .btn.primary');
  const step = () => wizard.querySelector('.wizard-step:not([hidden])').dataset.step;
  // One question per step: Enter moves on, and a step with a problem holds.
  assert.equal(step(), 'kind');
  assert.deepEqual([...wizard.querySelectorAll('.wizard-crumb')].map(c => c.textContent.replace(/\d/g, '')), ['Design', 'Outcome', 'Question', 'Test', 'Size', 'Name']);
  submit();
  assert.equal(step(), 'outcome');
  pick('outcome', 'continuous');
  pick('better', 'lower');
  pick('question', 'margin');
  assert.match(wizard.querySelector('.wizard-preview').textContent, /mean_difference_at_least\(model=study, value=1\/10\)/);
  assert.match(wizard.querySelector('.wizard-verdict').textContent, /cited from the literature/);
  // The blocks the study will have stack up beside the questions, in the canvas colours.
  assert.deepEqual([...wizard.querySelectorAll('.wiz-block')].map(b => b.dataset.name + ':' + b.dataset.family),
    ['study:study', 'design:design', 'null:null', 'analysis:analysis', 'checked:run']);
  [...wizard.querySelectorAll('.wizard-crumb')][4].click();
  assert.equal(step(), 'size');
  const control = wizard.querySelector('.wizard-step[data-step="size"] .wizard-pill');
  control.value = '5x';
  control.dispatchEvent(new window.Event('input', {bubbles: true}));
  assert.ok(next.disabled, 'a step with a problem holds');
  assert.equal(control.getAttribute('aria-invalid'), 'true');
  assert.match(wizard.querySelector('.wizard-problem').textContent, /whole number/);
  control.value = '50';
  control.dispatchEvent(new window.Event('input', {bubbles: true}));
  submit();
  assert.equal(step(), 'name');
  assert.equal(next.textContent, 'Create study');
  submit();
  await until(() => el('filename').textContent === 'my-study.stat', 'the wizard did not create a study');
  await ready();
  assert.equal(el('report').dataset.state, 'ready');
  assert.match(src.value, /t_test_one_sided\(design=design, null=null, alpha=1\/40\)/);
  assert.ok(host.querySelector('.stack-reading'), 'values read in words');
  assert.match(host.querySelector('.stack[data-name="analysis"] .stack-reading').textContent, /One-sided pooled-variance t-test of mean_treatment - mean_control >= 1\/10, at level 1\/40 \(2.5%\)/);

  // Practice: lesson 1 with its links emptied, and a checklist that ticks as they are filled.
  el('lesson').value = '01_first_claim.stat';
  el('lesson').dispatchEvent(new window.Event('change', {bubbles: true}));
  await ready();
  assert.ok(!el('practiceStart').hidden);
  el('practiceStart').click();
  await until(() => el('filename').textContent === 'practice-01_first_claim.stat', 'practice did not start');
  await ready();
  const card = el('practice');
  assert.ok(!card.hidden);
  assert.equal(card.querySelectorAll('.practice-step').length, 6);
  assert.match(card.querySelector('.practice-titles').textContent, /0 of 6 links/);
  assert.match(src.value, /let design = fixed\(model=choose_model\)/);
  card.querySelector('.practice-step .practice-hint .practice-answer').click();
  assert.equal(card.querySelector('.practice-step code').textContent, 'study');
  card.querySelector('.practice-step .practice-go').click();
  [...host.querySelectorAll('.pop .opt')].find(o => o.querySelector('.opt-label')?.textContent === 'study').click();
  await ready();
  assert.match(card.querySelector('.practice-titles').textContent, /1 of 6 links/);
  assert.equal(card.querySelector('.practice-step').dataset.state, 'right');
  // Filling every link the lesson's way finishes the exercise.
  src.value = readFileSync(new URL('01_first_claim.stat', tutorials), 'utf8');
  src.dispatchEvent(new window.Event('input', {bubbles: true}));
  await ready();
  assert.match(card.querySelector('.practice-done').textContent, /matches the lesson exactly/);

  // Why: a stack menu explains its contract with the checked derivation.
  const analysis = host.querySelector('.stack[data-name="analysis"]');
  analysis.querySelector('.hat-btn').click();
  [...host.querySelectorAll('.pop .menu-item')].find(item => item.textContent.startsWith('Why does it fit?')).click();
  await until(() => host.querySelector('.pop .why'), 'no explanation arrived');
  assert.match(host.querySelector('.pop .why').textContent, /The null and the design describe the same study model/);
  assert.match(host.querySelector('.pop .why-check').textContent, /independent checker/);
});

test('selecting a value or arming a block hints the palette blocks that take it', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  document.body.innerHTML = shell();
  await import(new URL('editor.js?hints', platform));
  const el = id => document.getElementById(id);
  const picker = el('lesson');
  const host = el('lessonBlocks');
  const palette = el('library');
  const strip = palette.querySelector('.pal-hint');
  const block = name => [...palette.querySelectorAll('.pal-block')].find(b => b.querySelector('.pal-name').textContent === name.replaceAll('_', ' '));
  const fit = name => block(name).dataset.fit;
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const pointer = (target, type) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: 5, clientY: 5, pointerId: 1}));
  const click = target => { pointer(target, 'pointerdown'); pointer(document, 'pointerup'); };
  await until(() => !picker.disabled && [...picker.options].some(o => o.value === '12_continuous_outcome.stat'), 'catalogue never loaded');
  picker.value = '12_continuous_outcome.stat';
  picker.dispatchEvent(new window.Event('change', {bubbles: true}));
  await until(() => !host.inert && stack('study') && stack('robust'), 'lesson 12 never rendered');

  // A continuous study: its nulls and designs take it, and the t-tests take it through a design.
  click(stack('study').querySelector('.hat'));
  assert.ok(stack('study').classList.contains('selected'));
  await until(() => !strip.hidden && fit('t_test'), 'no hints for a selected study');
  assert.match(strip.textContent, /blocks take study/);
  assert.equal(fit('fixed'), 'direct');
  assert.ok(block('fixed').querySelector('.pal-hole[data-param="model"]').classList.contains('hole-fit'), 'the input that takes it is marked');
  assert.equal(fit('equal_means'), 'direct');
  for (const name of ['t_test', 'welch_test', 'mmrm_test']) {
    assert.equal(fit(name), 'via', name);
    assert.equal(block(name).querySelector('.pal-fit').textContent, 'via fixed');
  }
  for (const name of ['fisher', 'log_rank', 'logistic_regression', 'cluster_t_test']) assert.equal(fit(name), undefined, name + ' does not fit a continuous study');
  assert.ok(palette.querySelector('.palette').classList.contains('hinting'));
  assert.ok([...palette.querySelectorAll('.rail-count')].some(c => !c.hidden), 'the rail counts hinted blocks');

  // Only these hides the rest; a design is taken by the tests directly.
  const only = strip.querySelector('.pal-hint-only');
  only.click();
  assert.ok(block('fisher').hidden && !block('t_test').hidden);
  only.click();
  assert.ok(!block('fisher').hidden);
  click(stack('plan').querySelector('.hat'));
  await until(() => fit('t_test') === 'direct', 'a design should be taken by the t-test directly');
  assert.ok(!stack('study').classList.contains('selected') && stack('plan').classList.contains('selected'));
  assert.ok(block('t_test').querySelector('.pal-hole[data-param="design"]').classList.contains('hole-fit'));

  // Escape ends the selection, and the hints with it.
  document.body.dispatchEvent(new window.KeyboardEvent('keydown', {key: 'Escape', bubbles: true}));
  await until(() => strip.hidden, 'Escape should end the hints');
  assert.equal(palette.querySelector('.pal-block[data-fit]'), null);
  assert.equal(host.querySelector('.stack.selected'), null);

  // An armed palette block hints what takes the value it makes.
  block('two_arm_binomial').click();
  await until(() => !strip.hidden && fit('fisher'), 'an armed block should hint what takes it');
  assert.equal(fit('fisher'), 'via');
  assert.equal(fit('t_test'), undefined);
  strip.querySelector('.pal-hint-close').click();
  await until(() => strip.hidden, 'closing the hints should disarm the block');
  assert.equal(block('two_arm_binomial').getAttribute('aria-pressed'), 'false');
});

test('open inputs that take the selected value are marked', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const post = (path, body) => dispatch(path, {method: 'POST', body: JSON.stringify(body)}).json();
  const host = document.createElement('main');
  document.body.append(host);
  const source = 'use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse tests.fisher\n' +
    'let study = two_arm_continuous(n_control=60, n_treatment=60)\nlet plan = fixed(model=study)\n' +
    'let first = t_test(design=choose_design, null=equal_means(model=study), alpha=1/20)\n' +
    'let second = fisher(design=choose_design, null=choose_null, alpha=1/20)\n';
  const selections = [];
  const doc = mountDocument(host, {...manifest, ...(await post('/api/parse', {source})), source, bindings: (await post('/api/compile', {source})).bindings,
    layout: null, onChange() {}, onSelect: name => selections.push(name)});
  doc.select('plan');
  assert.deepEqual(selections, ['plan']);
  const {fits} = await post('/api/fits', {source, declaration: 'plan'});
  doc.showFits('plan', fits);
  const slot = (name, param) => host.querySelector('.stack[data-name="' + name + '"] [data-slot="' + param + '"]');
  assert.equal(slot('first', 'design').dataset.fit, '', 'a t-test takes a continuous design');
  assert.equal(slot('second', 'design').dataset.fit, undefined, 'Fisher does not');
  assert.equal(slot('second', 'null').dataset.fit, undefined);
  doc.select(null);
  assert.equal(slot('first', 'design').dataset.fit, undefined);
  assert.deepEqual(selections, ['plan', null]);
});

test('an edit keeps the canvas where it was, without gliding back from the top', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {mountDocument} = await import(new URL('document.js', platform));
  const manifest = await dispatch('/api/blocks').json();
  const post = (path, body) => dispatch(path, {method: 'POST', body: JSON.stringify(body)}).json();
  const host = document.createElement('main');
  document.body.append(host);
  const scrolls = [];
  host.scrollTo = options => scrolls.push(options);
  const source = 'use models.two_arm_binomial\nlet study = two_arm_binomial(n_control=50, n_treatment=50)\n';
  mountDocument(host, {...manifest, ...(await post('/api/parse', {source})), source, bindings: (await post('/api/compile', {source})).bindings,
    layout: null, onChange() {}, scroll: {top: 640, left: 30}});
  assert.deepEqual(scrolls, [{top: 640, left: 30, behavior: 'instant'}], 'the redraw puts the scroll back at once');
});

test('a check block says what its run found, with the numbers', async () => {
  const window = new Window({url: 'http://localhost/'});
  install(window);
  const {headline, percent} = await import(new URL('ui.js', platform));
  const exact = (fraction, decimal) => ({fraction, decimal_approximation: decimal});
  // Shapes taken from examples/one_sample.stat and the other examples.
  const feasibility = {status: 'calculated', decision: 'target_not_met', calculation: {
    n: 25, critical_value: 9, power: exact('2165/2980', '0.726468549855427230'), minimum_power: exact('4/5', '0.8'),
    power_target_met: false, typeI: exact('1/21', '0.0467742'), maximum_typeI: exact('1/20', '0.05'), typeI_target_met: true}};
  assert.deepEqual(headline(feasibility), {text: 'Power 72.6% at n = 25, below the 80% target', tone: 'warn'});
  const sizing = {status: 'calculated', decision: 'target_met', calculation: {
    n_control: 36, n_treatment: 36, power: '0.800390263055211200', minimum_power: '0.8', power_target_met: true,
    typeI_target_met: true, min_per_arm: 20, max_per_arm: 60, candidates_evaluated: 17}};
  assert.equal(headline(sizing).text, 'Smallest size: 36 per arm, power 80.04%');
  assert.equal(headline({decision: 'target_met', calculation: {n_stage1: 13, n_stage2: 30, power: '0.8002', minimum_power: '0.8', power_target_met: true}}).text,
    'Power 80.02% at 13 then 30, meets the 80% target');
  assert.deepEqual(headline({decision: 'no_feasible_candidate', calculation: {min_n: 10, max_n: 20}}), {text: 'No size from 10 to 20 meets the target', tone: 'warn'});
  assert.equal(headline({decision: 'reject_null', calculation: {p_value: '0.00850357147862395534'}}).text, 'Reject the null, p = 0.0085');
  assert.equal(headline({decision: 'interval_reported', calculation: {level: '0.95', estimate: '0.4', lower: '0.2387', upper: '0.5789'}}).text,
    'Estimate 0.4, 95% interval 0.239 to 0.579');
  assert.equal(percent('0.025'), '2.5%');
  assert.equal(percent('0.7999', '0.8'), '79.99%');
  // Observational studies, in the units their design fixes (shapes from the lessons).
  const search = {power: '0.8003', minimum_power: '0.8', power_target_met: true, candidates_evaluated: 84};
  assert.equal(headline({decision: 'target_met', calculation: {...search, cases: 133, controls: 266}}).text,
    'Smallest size: 133 cases and 266 controls, power 80.03%');
  assert.equal(headline({decision: 'target_met', calculation: {...search, pairs: 298}}).text, 'Smallest size: 298 pairs, power 80.03%');
  assert.equal(headline({decision: 'target_met', calculation: {...search, events: 94}}).text, 'Smallest size: 94 events, power 80.03%');
  assert.equal(headline({decision: 'target_met', calculation: {...search, total_sample_size: 148, exposed_share: '0.3'}}).text,
    'Smallest size: n = 148, power 80.03%');
  assert.equal(headline({decision: 'target_not_met', calculation: {power: '0.7603', minimum_power: '0.8', power_target_met: false,
    exposed: 150, unexposed: 300}}).text, 'Power 76% at 150 exposed and 300 unexposed, below the 80% target');
  assert.equal(headline({decision: 'no_feasible_candidate', calculation: {min_cases: 10, max_cases: 60}}).text,
    'No size from 10 to 60 meets the target');
  assert.equal(headline({decision: 'no_feasible_candidate', calculation: {min_pairs: 10, max_pairs: 40}}).text,
    'No size from 10 to 40 meets the target');
  // Cluster trials, in clusters and their size; a size search says how far participants can go.
  const clusters = {clusters_control: 8, clusters_treatment: 8, cluster_size_control: {fraction: '20'}, cluster_size_treatment: {fraction: '20'}};
  assert.equal(headline({decision: 'target_met', calculation: {...search, ...clusters, n_control: 160, n_treatment: 160}}).text,
    'Smallest size: 8 clusters of 20 per arm, power 80.03%');
  assert.equal(headline({decision: 'target_not_met', calculation: {power: '0.71', minimum_power: '0.8', power_target_met: false,
    ...clusters, clusters_treatment: 6, cluster_size_treatment: {fraction: '125/6', decimal_approximation: '20.833333'}}}).text,
  'Power 71% at 8 and 6 clusters of 20 and 20.8, below the 80% target');
  assert.equal(headline({decision: 'target_met', calculation: {...search, ...clusters, cluster_size_cv: {fraction: '3/5'}, n_control: 160, n_treatment: 160}}).text,
    'Smallest size: 8 clusters of 20 per arm on average, power 80.03%');
  // A design with looks shows how often each look stopped the trial, and the expected size.
  {
    const {calculationLines} = await import(new URL('ui.js', platform));
    const lines = calculationLines({power: '0.93', power_lower: '0.92', power_upper: '0.94', minimum_power: '0.8', power_target_met: true,
      typeI: '0.048', typeI_lower: '0.044', typeI_upper: '0.052', alpha: '0.05', runs: 10000, seed: 1, n_control: 100, n_treatment: 100,
      looks: [{n_control: 50, n_treatment: 50, stop: '0.36', stop_null: '0.005'}, {n_control: 100, n_treatment: 100, stop: '0.57', stop_null: '0.043'}],
      expected_sample_size: {decimal_approximation: '163.8'}, expected_sample_size_null: {decimal_approximation: '199.5'}}, 'target_met');
    const looks = lines.find(([label]) => label === 'Looks');
    assert.ok(looks && /50 and 50: stops 36%/.test(looks[1]), JSON.stringify(lines));
    assert.deepEqual(lines.find(([label]) => label === 'Expected size').slice(0, 2), ['Expected size', '164 participants']);
  }
  // Fisher's test at looks: exact stopping, expected size and Type I at the control rate.
  {
    const {calculationLines} = await import(new URL('ui.js', platform));
    const record = value => ({decimal_approximation: value});
    const lines = calculationLines({power: record('0.7858'), minimum_power: '0.8', power_target_met: false, n_control: 100, n_treatment: 100,
      looks: [{n_control: 50, n_treatment: 50, stop: record('0.1776'), stop_null: record('0.0028')}, {n_control: 100, n_treatment: 100, stop: record('0.6082'), stop_null: record('0.03')}],
      expected_sample_size: record('182.2'), expected_sample_size_null: record('199.7'), typeI_at_control_rate: record('0.0328')}, 'target_not_met');
    assert.ok(lines.find(([label]) => label === 'Looks'), JSON.stringify(lines));
    assert.deepEqual(lines.find(([label]) => label === 'Expected size').slice(0, 2), ['Expected size', '182 participants']);
    assert.ok(lines.find(([label]) => label === 'Exact Type I'));
  }
  // A family lists each endpoint's power, and any and all.
  {
    const {calculationLines} = await import(new URL('ui.js', platform));
    const rate = (r, l, u) => ({rate: r, lower: l, upper: u});
    const lines = calculationLines({power: '0.92', power_lower: '0.91', power_upper: '0.93', minimum_power: '0.8', power_target_met: true,
      typeI: '0.038', typeI_lower: '0.034', typeI_upper: '0.042', alpha: '0.05', runs: 10000, seed: 1, n_control: 120, n_treatment: 120,
      endpoints: [{name: 'response', power: rate('0.80', '0.79', '0.81')}, {name: 'symptoms', power: rate('0.80', '0.79', '0.81')}],
      power_any: rate('0.92', '0.91', '0.93'), power_all: rate('0.67', '0.66', '0.68')}, 'target_met');
    assert.ok(lines.find(([label]) => label === 'Response'), JSON.stringify(lines));
    assert.ok(lines.find(([label]) => label === 'All'));
  }
  // A re-estimated design lists Type I at each null scenario.
  {
    const {calculationLines} = await import(new URL('ui.js', platform));
    const lines = calculationLines({power: '0.79', power_lower: '0.78', power_upper: '0.80', minimum_power: '0.75', power_target_met: true,
      typeI: '0.051', typeI_lower: '0.047', typeI_upper: '0.055', alpha: '0.05', runs: 10000, seed: 1, n_control: 64, n_treatment: 64,
      initial_per_arm: 64, interim_per_arm: 30, max_per_arm: 200, expected_sample_size: {decimal_approximation: '254.4'},
      null_scenarios: [{sd: {fraction: '6'}, typeI: '0.0507', typeI_lower: '0.0465', typeI_upper: '0.0552', expected_sample_size: {decimal_approximation: '128'}}]}, 'target_met');
    assert.deepEqual(lines.find(([label]) => label === 'Re-estimated').slice(0, 2), ['Re-estimated', 'After 30 per arm, 64 to 200 per arm']);
    assert.ok(lines.find(([label]) => label === 'Type I at SD 6'), JSON.stringify(lines));
  }
  // A judged Type I can leave a simulation undecided even when power is settled.
  assert.equal(headline({decision: 'undecided', calculation: {power: '0.9', power_lower: '0.89', power_upper: '0.91', minimum_power: '0.8',
    power_target_met: true, power_settled: true, typeI: '0.075', typeI_target_met: false, typeI_settled: false, typeI_judged: true,
    maximum_typeI: '0.075', n_control: 40, n_treatment: 40}}).text,
  'Power 90% (89–91%) at 40 per arm: undecided, the type I interval includes the 7.5% limit');
  // A survey says what its total is worth.
  assert.equal(headline({decision: 'target_met', calculation: {...search, total_sample_size: 23530, covariates: 0, effective_sample_size: {decimal_approximation: '11765.000000'}}}).text,
    'Smallest size: n = 23530 (effectively 11765), power 80.03%');
  // A precision target: the margin reached, and the assurance when asked.
  assert.equal(headline({decision: 'target_met', calculation: {margin_achieved: {decimal_approximation: '0.03'}, target_margin: {fraction: '3/100'},
    relative: false, precision_target_met: true, total_sample_size: 417, candidates_evaluated: 14}}).text, 'Smallest size: n = 417, margin ±0.03');
  assert.deepEqual(headline({decision: 'target_not_met', calculation: {margin_achieved: {decimal_approximation: '0.030650'}, target_margin: {fraction: '3/100'},
    relative: false, precision_target_met: false, total_sample_size: 400}}), {text: 'Margin ±0.0307 at n = 400, short of the ±0.03 target', tone: 'warn'});
  assert.equal(headline({decision: 'target_met', calculation: {margin_achieved: {decimal_approximation: '0.4917'}, target_margin: {fraction: '1/2'}, relative: true,
    assurance: {decimal_approximation: '0.8045'}, minimum_assurance: {fraction: '4/5'}, precision_target_met: true, cases: 177, controls: 354, candidates_evaluated: 13}}).text,
  'Sufficient size: 177 cases and 354 controls, relative margin 49.2%, assurance 80.5%');
  // A cited observational test, by its total.
  assert.equal(headline({decision: 'target_met', calculation: {...search, total_sample_size: 193, covariates: 0}}).text,
    'Smallest size: n = 193, power 80.03%');
  // A survival plan from times says how many events its size expects.
  assert.equal(headline({decision: 'target_met', calculation: {...search, n_control: 202, n_treatment: 202, expected_events: {decimal_approximation: '247.953230'}}}).text,
    'Smallest size: 202 per arm (about 248 events), power 80.03%');
  assert.equal(headline({decision: 'no_feasible_candidate', calculation: {min_cluster_size: 2, max_cluster_size: 300,
    power_ceiling: {decimal_approximation: '0.318112'}}}).text,
  'No size from 2 to 300 meets the target; with these clusters power cannot pass 31.8%');
  window.happyDOM.close();
});

test('values a run fills in show on their blocks', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  const canned = {status: 'calculated', run_directory: null, certificate_issued: false, diagnostics: [], requests: [],
    values: {recommended_n: 35, critical_value: 12}};
  globalThis.fetch = async (url, options = {}) => url === '/api/run' ? new Response(JSON.stringify(canned)) : dispatch(url, options);
  document.body.innerHTML = shell();
  await import(new URL('editor.js?values', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const picker = el('lesson');
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !picker.disabled && [...picker.options].some(o => o.value === 'example/one_sample.stat'), 'examples never loaded');
  picker.value = 'example/one_sample.stat';
  picker.dispatchEvent(new window.Event('change', {bubbles: true}));
  await until(() => stack('recommended_n'), 'the example did not open');
  await ready();
  assert.equal(host.querySelector('.value-bubble'), null, 'nothing shows before a run');
  el('runChecks').click();
  await until(() => host.querySelector('.value-bubble'), 'values never showed');
  assert.equal(stack('recommended_n').querySelector('.value-bubble .value-text').textContent, '35');
  assert.equal(stack('critical_value').querySelector('.value-bubble .value-text').textContent, '12');
  assert.equal(stack('study').querySelector('.value-bubble'), null, 'declared values need no run');
  assert.equal(stack('recommended_n').querySelector('.hat-value').textContent, '= 35');
  const listed = [...el('results').querySelectorAll('.value-list li')].map(li => li.textContent);
  assert.deepEqual(listed, ['recommended_n=35', 'critical_value=12']);
  // An edit leaves the values in place, marked as from the last run.
  const size = stack('study').querySelector('input[aria-label="n"]');
  size.value = '30';
  size.dispatchEvent(new window.Event('change', {bubbles: true}));
  await ready();
  assert.equal(stack('recommended_n').querySelector('.value-bubble').dataset.stale, 'true');
  assert.match(stack('recommended_n').querySelector('.value-bubble').title, /changed since/);
});

test('numbers change by dragging, in steps that suit them', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  const {scrubber} = await import(new URL('ui.js', platform));
  const at = (text, expected, steps, shift = false) => scrubber(text, expected).at(steps, shift);
  assert.equal(at('25', 'integer', 3), '28');
  assert.equal(at('25', 'integer', 2, true), '45');
  assert.equal(at('3', 'integer', -9), '0', 'sizes do not go below zero');
  assert.equal(at('1/20', 'level', 1), '1/10');
  assert.equal(at('1/20', 'level', -1), '1/40');
  assert.equal(at('0.03', 'level', 1), '1/20', 'off the ladder, the first step goes to the next level');
  assert.equal(at('0.03', 'level', -1), '1/40');
  assert.equal(at('1/20', 'level', 40), '1/5');
  assert.equal(at('2/5', 'exact number', 1), '41/100');
  assert.equal(at('2/5', 'exact number', 10), '1/2');
  assert.equal(at('0.4', 'exact number', 2), '0.42');
  assert.equal(at('2/5', 'exact number', 100), '99/100', 'rates stay below one');
  assert.equal(at('-1/10', 'exact number', 1), '-9/100');
  assert.equal(at('2.5', 'exact number', 3), '2.8');
  assert.equal(at('12.5', 'exact number', 1), '13.5');
  assert.equal(scrubber('', 'integer'), null);

  // On the canvas: drag the sample size of lesson 1 to the right, and the level along its ladder.
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  document.body.innerHTML = shell();
  await import(new URL('editor.js?scrub', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const src = el('source');
  const picker = el('lesson');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  const pointer = (target, type, x, extra = {}) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: 10, pointerId: 1, ...extra}));
  await until(() => !picker.disabled && host.querySelector('.stack'), 'editor never loaded');
  picker.value = '01_first_claim.stat';
  picker.dispatchEvent(new window.Event('change', {bubbles: true}));
  await ready();
  const size = () => host.querySelector('.stack[data-name="study"] input[aria-label="n control"]');
  assert.ok(size().classList.contains('scrubbable'));
  const before = size().value;
  pointer(size(), 'pointerdown', 100);
  pointer(window, 'pointermove', 102);
  assert.equal(size().value, before, 'a small wobble is still a click');
  pointer(window, 'pointermove', 100 + 7 * 5 + 2);
  assert.equal(size().value, String(Number(before) + 5));
  assert.ok(document.body.classList.contains('scrubbing'));
  pointer(window, 'pointerup', 137);
  await ready();
  assert.match(src.value, new RegExp('n_control=' + (Number(before) + 5)));
  assert.equal(document.body.classList.contains('scrubbing'), false);
  el('undo').click();
  await ready();
  assert.match(src.value, new RegExp('n_control=' + before + '\\b'));
  // Escape puts the number back without an edit.
  const source = src.value;
  pointer(size(), 'pointerdown', 100);
  pointer(window, 'pointermove', 160);
  window.dispatchEvent(new window.KeyboardEvent('keydown', {key: 'Escape', bubbles: true}));
  pointer(window, 'pointerup', 160);
  await ready();
  assert.equal(src.value, source);
  assert.equal(size().value, before);
  // A click without moving types instead.
  pointer(size(), 'pointerdown', 100);
  pointer(window, 'pointerup', 100);
  assert.equal(document.activeElement, size());
  size().blur();
  const level = host.querySelector('input[aria-label="alpha"]');
  assert.equal(level.value, '1/20');
  pointer(level, 'pointerdown', 100);
  pointer(window, 'pointermove', 100 + 18 + 1);
  pointer(window, 'pointerup', 119);
  await ready();
  assert.match(src.value, /alpha=1\/10/);
});

test('after a number is dragged, the calculations follow and proofs wait for the next run', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  // examples/one_sample.stat: calculation on line 14, recommendation on 19, verification on 20.
  const check = (id, name, operation, claim, subject, line, column, extra) => ({request_id: id, name, operation, claim, subject,
    source: {line, column, end_line: line, end_column: column + 20}, established: [], assumptions: [], references: [], ...extra});
  const feasibility = n => ({status: 'calculated', decision: n === 25 ? 'target_not_met' : 'target_met',
    calculation: {n, power: n === 25 ? '0.7265' : '0.8048', minimum_power: '0.8', power_target_met: n !== 25}});
  const full = {status: 'verified', run_directory: '/tmp/run', certificate_issued: true, diagnostics: [],
    requests: [
      check(1, 'calculation', 'calculate', 'meets', 'analysis', 14, 19, feasibility(25)),
      check(2, 'recommendation', 'calculate', 'sample_size', 'candidates', 19, 22, feasibility(35)),
      check(3, 'verification', 'verify', 'sample_size', 'candidates', 20, 20, {status: 'verified', evidence: {grade: 'proved', scope: 'finite_sample'}}),
    ],
    values: {recommended_n: 35, critical_value: 12}};
  const partial = {status: 'calculated', run_directory: null, certificate_issued: false, diagnostics: [],
    requests: [
      check(1, 'calculation', 'calculate', 'meets', 'analysis', 14, 19, feasibility(30)),
      check(2, 'recommendation', 'calculate', 'sample_size', 'candidates', 19, 22, feasibility(35)),
      check(3, 'verification', 'verify', 'sample_size', 'candidates', 20, 20, {status: 'not_executed'}),
    ],
    values: {recommended_n: 36}};
  const runs = [];
  globalThis.fetch = async (url, options = {}) => {
    if (url !== '/api/run') return dispatch(url, options);
    const body = JSON.parse(options.body);
    runs.push(body.only || 'all');
    return new Response(JSON.stringify(body.only ? partial : full));
  };
  document.body.innerHTML = shell();
  await import(new URL('editor.js?recalculate', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const picker = el('lesson');
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  const pointer = (target, type, x) => target.dispatchEvent(new window.PointerEvent(type, {bubbles: true, button: 0, clientX: x, clientY: 10, pointerId: 1}));
  await until(() => !picker.disabled && [...picker.options].some(o => o.value === 'example/one_sample.stat'), 'examples never loaded');
  picker.value = 'example/one_sample.stat';
  picker.dispatchEvent(new window.Event('change', {bubbles: true}));
  await until(() => stack('recommended_n'), 'the example did not open');
  await ready();
  // Without a run, dragging only edits.
  el('runChecks').click();
  await until(() => host.querySelector('.value-bubble'), 'the run never finished');
  assert.match(stack('calculation').querySelector('.tray-headline').textContent, /at n = 25/);
  const size = stack('study').querySelector('input[aria-label="n"]');
  pointer(size, 'pointerdown', 100);
  pointer(window, 'pointermove', 100 + 7 * 5 + 1);
  pointer(window, 'pointerup', 136);
  await until(() => runs.length === 2, 'the drag did not recalculate');
  assert.deepEqual(runs, ['all', 'calculate']);
  await until(() => /at n = 30/.test(stack('calculation')?.querySelector('.tray-headline')?.textContent || ''), 'the calculation did not follow');
  assert.equal(stack('calculation').querySelector('.result-line').dataset.stale, undefined, 'a fresh calculation is current');
  const proof = stack('verification').querySelector('.result-line');
  assert.equal(proof.dataset.stale, 'true', 'the proof is from before the edit');
  assert.equal(stack('verification').querySelector('.cert-stamp').dataset.stale, 'true');
  assert.equal(stack('calculation').querySelector('.cert-stamp'), null);
  assert.match(proof.textContent, /Proved in Lean/);
  assert.equal(stack('recommended_n').querySelector('.value-text').textContent, '36');
  assert.equal(stack('recommended_n').querySelector('.value-bubble').dataset.stale, undefined);
  assert.equal(stack('critical_value').querySelector('.value-bubble').dataset.stale, 'true');
  assert.match(el('results').textContent, /Calculations follow your last edit/);
  // A typed edit does not recalculate; it marks everything outdated as before.
  const typed = stack('study').querySelector('input[aria-label="n"]');
  typed.value = '40';
  typed.dispatchEvent(new window.Event('change', {bubbles: true}));
  await ready();
  assert.equal(runs.length, 2);
  assert.equal(stack('calculation').querySelector('.result-tray').dataset.stale, 'true');
});

test('simulations show their intervals, and a simulated search draws its power curve', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  const {headline} = await import(new URL('ui.js', platform));
  const record = (fraction, decimal) => ({fraction, decimal_approximation: decimal});
  const simulated = {n_control: 40, n_treatment: 40, power: record('6025/10000', '0.6025'), power_lower: record('148/250', '0.592800'),
    power_upper: record('6121/10000', '0.612100'), minimum_power: record('4/5', '0.8'), power_target_met: false, power_settled: true,
    typeI: record('509/10000', '0.0509'), typeI_lower: record('467/10000', '0.046700'), typeI_upper: record('277/5000', '0.055400'),
    alpha: record('1/20', '0.05'), typeI_target_met: true, runs: 10000, seed: 2026, scenario: 'normal outcomes with standard deviation 10'};
  assert.deepEqual(headline({status: 'simulated', decision: 'target_not_met', calculation: simulated}),
    {text: 'Power 60.3% (59.3–61.2%) at 40 per arm, below the 80% target', tone: 'warn'});
  assert.equal(headline({status: 'simulated', decision: 'undecided', calculation: {...simulated, power_target_met: false, power_settled: false}}).text,
    'Power 60.3% (59.3–61.2%) at 40 per arm: undecided, the interval includes the 80% target');
  const curve = [60, 61, 62, 63, 64, 65].map((n, i) => ({n_control: n, n_treatment: n, power: 0.76 + i * 0.01, lower: 0.75 + i * 0.01, upper: 0.77 + i * 0.01}));
  const sizing = {...simulated, n_control: 65, n_treatment: 65, power: record('809/1000', '0.809'), power_lower: record('801/1000', '0.8012'),
    power_upper: record('817/1000', '0.8167'), power_target_met: true, candidates_evaluated: 46, confirmations: 1, min_per_arm: 20, max_per_arm: 120, curve};
  assert.equal(headline({status: 'simulated', decision: 'target_met', calculation: sizing}).text, 'Smallest size: 65 per arm, power 80.9% (80.1–81.7%)');

  // examples/tutorial/28_simulated_power.stat: formula on line 15, simulated on 16, sizing on 20.
  const check = (id, name, operation, claim, subject, line, column, extra) => ({request_id: id, name, operation, claim, subject,
    source: {line, column, end_line: line, end_column: column + 30}, established: [], assumptions: [], references: [], evidence: null, ...extra});
  const canned = {status: 'simulated', run_directory: '/tmp/run', certificate_issued: false, diagnostics: [], values: {per_arm: 65},
    requests: [
      check(1, 'formula', 'calculate', 'meets', 'analysis', 15, 15, {status: 'calculated', decision: 'target_not_met',
        calculation: {n_control: 40, n_treatment: 40, power: '0.608796', minimum_power: '0.8', power_target_met: false}}),
      check(2, 'simulated', 'simulate', 'meets', 'analysis', 16, 17, {status: 'simulated', decision: 'target_not_met', calculation: simulated}),
      check(3, 'sizing', 'simulate', 'sample_size', 'sizes', 20, 14, {status: 'simulated', decision: 'target_met', calculation: sizing}),
    ]};
  globalThis.fetch = async (url, options = {}) => url === '/api/run' ? new Response(JSON.stringify(canned)) : dispatch(url, options);
  document.body.innerHTML = shell();
  await import(new URL('editor.js?simulate', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const picker = el('lesson');
  const src = el('source');
  const stack = name => host.querySelector('.stack[data-name="' + name + '"]');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !picker.disabled && host.querySelector('.stack'), 'editor never loaded');
  // Before any run, the legend explains every grade, simulated included.
  assert.match(el('results').textContent, /Simulated, not a proof/);
  picker.value = '28_simulated_power.stat';
  picker.dispatchEvent(new window.Event('change', {bubbles: true}));
  await until(() => stack('sizing'), 'lesson 28 did not open');
  await ready();
  assert.match(stack('sizing').querySelector('.result-tray').textContent, /Run check/, 'a simulation is a check block');
  el('runChecks').click();
  await until(() => host.querySelector('.result-tray[data-state="done"]'), 'run results never appeared');
  const tray = stack('simulated').querySelector('.result-tray');
  assert.equal(tray.querySelector('.outcome').dataset.tone, 'simulated');
  assert.equal(tray.querySelector('.outcome').textContent, 'Simulated');
  assert.equal(host.querySelector('.cert-stamp'), null, 'estimates earn no medal');
  assert.equal(tray.querySelector('.tray-headline').textContent, 'Power 60.3% (59.3–61.2%) at 40 per arm, below the 80% target');
  assert.equal(stack('per_arm').querySelector('.value-text').textContent, '65');
  // The Results entry of the search holds its curve, with a table of the same numbers.
  const entry = el('results').querySelector('.result-entry[data-request="3"]');
  assert.match(entry.querySelector('.entry-facts').textContent, /Runs10,000 per estimate, seed 2026/);
  const figure = entry.querySelector('.power-curve');
  assert.ok(figure.querySelector('polyline.curve-line') && figure.querySelector('polygon.curve-band') && figure.querySelector('.curve-target'));
  assert.match(figure.querySelector('svg').getAttribute('aria-label'), /65 per arm reaches the target/);
  assert.equal(figure.querySelectorAll('.curve-table tr').length, curve.length + 1);
  assert.equal(figure.querySelector('.curve-table tr.chosen td').textContent, '65 per arm');
  assert.equal(el('results').querySelector('.result-entry[data-request="2"] .power-curve'), null, 'one size has no curve');
  // The seed can be rerolled from its block.
  const roll = stack('sizing').querySelector('.seed-roll');
  assert.ok(roll);
  roll.click();
  await ready();
  assert.doesNotMatch(src.value.split('\n')[19], /seed=2026\)/);
  assert.match(src.value.split('\n')[19], /seed=\d+\)/);
});

test('the wizard can plan a continuous outcome by simulation', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {studySource, plannable, available} = await import(new URL('wizard.js', platform));
  const effects = {differ: '5', better: {higher: '5', lower: '-5'}, margin: {higher: '0', lower: '0'}};
  for (const better of ['higher', 'lower']) {
    for (const question of ['differ', 'better', 'margin']) {
      if (!available('continuous', better)[question]) continue;
      const effect = typeof effects[question] === 'string' ? effects[question] : effects[question][better];
      assert.equal(plannable({question, better, margin: '2', effect}), '');
      const made = studySource({outcome: 'continuous', better, question, margin: '2', plan: true, effect, sd: '10', seed: 3});
      const result = await (await dispatch('/api/compile', {method: 'POST', body: JSON.stringify({source: made.source, name: 'x.stat'})})).json();
      assert.deepEqual(result.diagnostics.filter(d => d.severity === 'error'), [], better + ' ' + question + '\n' + made.source);
      assert.match(made.source, /simulate\(smallest_sample_size\(candidates=sizes, target=target\), seed=3\)/);
    }
  }
  assert.match(plannable({question: 'margin', better: 'higher', margin: '2', effect: '-3'}), /above -2/);
  assert.doesNotMatch(studySource({outcome: 'binary', plan: true}).source, /simulate/, 'only continuous outcomes are simulated');
});

test('the wizard plans every observational design by exact power', async t => {
  const window = new Window({url: 'http://localhost/'});
  t.after(() => window.happyDOM.close());
  install(window);
  const {observationalSource, observationalPlannable} = await import(new URL('wizard.js', platform));
  const compile = source => dispatch('/api/compile', {method: 'POST', body: JSON.stringify({source})}).json();
  const searches = {cohort: 'cohort_sizes', population: 'total_sizes', case_control: 'case_control_sizes',
    cross_sectional: 'total_sizes', matched_case_control: 'matched_sizes'};
  for (const [design, population] of [['cohort', false], ['cohort', true], ['case_control', false], ['cross_sectional', false], ['matched_case_control', false]]) {
    const point = {design, population, base: '1/10', ratio: '2', share: '3/10'};
    assert.equal(observationalPlannable(point), '', design);
    const made = observationalSource({...point, plan: true, exposure: 'night shifts', outcome: 'insomnia'});
    const result = await compile(made.source);
    assert.deepEqual(result.diagnostics, [], design + '\n' + made.source);
    assert.match(made.source, new RegExp(searches[population ? 'population' : design] + '\\(analysis=analysis'));
    assert.equal(result.bindings.expected.type.length > 0, true);
    assert.ok(result.bindings.expected.reading, design + ': the planning point reads in words');
  }
  // Cases with twice as many controls are searched with two controls per case.
  assert.match(observationalSource({design: 'case_control', cases: 100, controls: 200, plan: true}).source,
    /case_control_sizes\(analysis=analysis, min_cases=10, max_cases=250, controls_per_case=2\)/);
  assert.match(observationalPlannable({design: 'cohort', base: '1/2', ratio: '3'}), /above 1/);
  assert.match(observationalPlannable({design: 'case_control', base: '1/5', ratio: '1'}), /no association/);
  assert.match(observationalPlannable({design: 'cross_sectional', base: '1/10', ratio: '2', share: '1'}), /share/);
  assert.doesNotMatch(observationalSource({design: 'cohort'}).source, /use planning/, 'planning only when asked');
  // Two measured variables: Pearson's correlation and the slope are planned at their own points.
  const measured = {design: 'cross_sectional', outcomeScale: 'continuous', exposureScale: 'continuous', plan: true, exposure: 'BMI', outcome: 'pressure'};
  for (const [test, point] of [['pearson_correlation', /correlation\(value=1\/5\)/], ['linear_association', /slope\(value=1\/2, exposure_sd=4, residual_sd=15\)/]]) {
    assert.equal(observationalPlannable({...measured, test}), '', test);
    const made = observationalSource({...measured, test});
    assert.match(made.source, point);
    assert.match(made.source, /total_sizes\(analysis=analysis/);
    assert.deepEqual((await compile(made.source)).diagnostics, [], test + '\n' + made.source);
    assert.match(made.notes.join(' '), /cannot be verified/);
  }
  assert.match(observationalPlannable({...measured, test: 'pearson_correlation', rho: '0'}), /no association/);
  // With skewed data, Pearson's test and the slope test are simulated, and their Type I judged.
  {
    const {skewable} = await import(new URL('designs.js', platform));
    assert.ok(skewable({...measured, test: 'pearson_correlation'}));
    assert.ok(skewable({...measured, test: 'linear_association', covariates: ''}));
    assert.ok(!skewable({...measured, test: 'spearman_correlation'}));
    assert.ok(!skewable({...measured, test: 'linear_association', covariates: 'age'}));
    for (const [test, point] of [['pearson_correlation', /correlation\(value=1\/5, skewness=3, exposure_skewness=3\)/],
      ['linear_association', /slope\(value=1\/2, exposure_sd=4, residual_sd=15, skewness=3, exposure_skewness=3\)/]]) {
      const made = observationalSource({...measured, test, covariates: '', skewY: '3', skewX: '3', seed: 7});
      assert.match(made.source, point);
      assert.match(made.source, /maximum_typeI=3\/40\)/);
      assert.match(made.source, /simulate\(smallest_sample_size\(candidates=sizes, target=target\), seed=7, runs=2000\)/);
      assert.deepEqual((await compile(made.source)).diagnostics, [], test + '\n' + made.source);
    }
  }
  // The cited regressions are planned at the design's own point, and search beyond exact limits.
  const regressions = [
    [{design: 'cohort', exposed: 300, unexposed: 600, test: 'logistic_association'}, /cohort_sizes\(analysis=analysis, min_exposed=10, max_exposed=33333, unexposed_per_exposed=2\)/],
    [{design: 'case_control', cases: 150, controls: 300, test: 'logistic_association'}, /exposure_prevalence\(controls=1\/10, odds_ratio=2\)/],
    [{design: 'cross_sectional', exposureScale: 'continuous', test: 'logistic_association'}, /odds_per_sd\(odds_ratio=2, baseline=1\/10\)/],
    [{design: 'matched_case_control', cases: 220, test: 'conditional_logistic'}, /matched_sizes\(analysis=analysis, min_pairs=10, max_pairs=40000\)/],
    [{design: 'person_time', test: 'poisson_rate_regression'}, /event_counts\(analysis=analysis, min_events=10, max_events=50000\)/],
  ];
  // A survey test of a complex sample is planned with its design effect.
  regressions.push([{design: 'cross_sectional', survey: 'cluster', clusters: 100, test: 'rao_scott_test'},
    /outcome_prevalence\(unexposed=1\/10, prevalence_ratio=2, exposed_share=3\/10, design_effect=2\)/]);
  regressions.push([{design: 'cross_sectional', survey: 'stratified', exposureScale: 'continuous', outcomeScale: 'continuous', test: 'survey_linear'},
    /slope\(value=1\/2, exposure_sd=4, residual_sd=15, design_effect=2\)/]);
  assert.match(observationalPlannable({design: 'cross_sectional', survey: 'cluster', test: 'rao_scott_test', deff: '0'}), /design effect/);
  // Every cited test can be planned: a risk ratio, ranks, and two means by a yes-or-no exposure.
  regressions.push([{design: 'cohort', exposed: 300, unexposed: 600, test: 'modified_poisson'}, /risks\(unexposed=1\/10, risk_ratio=2\)/]);
  regressions.push([{design: 'cross_sectional', outcomeScale: 'continuous', exposureScale: 'continuous', test: 'spearman_correlation'}, /correlation\(value=1\/5\)/]);
  regressions.push([{design: 'cohort', exposed: 100, unexposed: 200, outcomeScale: 'continuous', test: 'linear_association'},
    /outcome_means\(unexposed=120, exposed=125, sd=15\)[\s\S]*cohort_sizes\(analysis=analysis, min_exposed=10, max_exposed=33333, unexposed_per_exposed=2\)/]);
  regressions.push([{design: 'cross_sectional', outcomeScale: 'continuous', test: 'linear_association'}, /outcome_means\(unexposed=120, exposed=125, sd=15, exposed_share=3\/10\)/]);
  regressions.push([{design: 'cross_sectional', outcomeScale: 'continuous', survey: 'weighted', test: 'survey_linear'},
    /outcome_means\(unexposed=120, exposed=125, sd=15, exposed_share=3\/10, design_effect=2\)/]);
  assert.match(observationalPlannable({design: 'cohort', outcomeScale: 'continuous', test: 'linear_association', meanExposed: '120'}), /cannot be equal/);
  // Clusters of unequal sizes are simulated, with the variation on the planning point.
  {
    const {studySource} = await import(new URL('designs.js', platform));
    const base = {outcome: 'continuous', unit: 'clusters', control: 120, treatment: 120, clustersControl: 6, clustersTreatment: 6, test: 'cluster_t_test', add: 'plan'};
    assert.match(studySource(base).source, /let power = calculate\(meets/);
    const varied = studySource({...base, cv: '3/5', seed: 7});
    assert.match(varied.source, /icc=1\/20, cluster_size_cv=3\/5\)/);
    assert.match(varied.source, /let sizing = simulate\(smallest_sample_size\(candidates=sizes, target=target\), seed=7\)/);
    assert.deepEqual((await compile(varied.source)).diagnostics, [], varied.source);
  }
  // A simulated t-test in another scenario: Type I is judged, against 1.5 times alpha.
  {
    const {studySource} = await import(new URL('designs.js', platform));
    const base = {outcome: 'continuous', control: 40, treatment: 40, test: 't_test', add: 'plan', seed: 7};
    const plain = studySource(base).source;
    assert.match(plain, /let expected = mean_difference\(value=5, sd=10\)/);
    assert.match(plain, /maximum_typeI=1\/20\)/);
    if (/simulate\(/.test(plain)) {
      const varied = studySource({...base, sdTreatment: '15', skew: '2'}).source;
      assert.match(varied, /mean_difference\(value=5, sd=10, sd_treatment=15, skewness=2\)/);
      assert.match(varied, /maximum_typeI=3\/40\)/);
      assert.match(varied, /seed=7, runs=2000\)/);
      assert.deepEqual((await compile(varied)).diagnostics, [], varied);
      // The same SD in both arms is the plain scenario.
      assert.equal(studySource({...base, sdTreatment: '10'}).source, plain);
    }
  }
  // A survival trial whose treatment acts late is simulated at its declared size.
  {
    const {studySource} = await import(new URL('designs.js', platform));
    const base = {outcome: 'survival', control: 200, treatment: 200, test: 'log_rank', add: 'plan', seed: 7};
    const plain = studySource(base).source;
    assert.doesNotMatch(plain, /simulate\(/);
    const late = studySource({...base, delay: '3'}).source;
    assert.match(late, /effect_delay=3\)/);
    assert.match(late, /let delayed_power = simulate\(meets\(analysis=analysis, target=delayed\), seed=7\)/);
    assert.deepEqual((await compile(late)).diagnostics, [], late);
  }
  // An interim look on a measured outcome: power, stopping and the expected size, simulated.
  {
    const {interimSource} = await import(new URL('designs.js', platform));
    const plain = interimSource({outcome: 'continuous'}).source;
    assert.doesNotMatch(plain, /simulate\(/);
    const made = interimSource({outcome: 'continuous', interimAdd: 'power', seed: 7});
    assert.match(made.source, /use planning/);
    assert.match(made.source, /let power = simulate\(meets\(analysis=trial, target=target\), seed=7\)/);
    assert.match(made.source, /power\.calculation\.expected_sample_size/);
    assert.deepEqual((await compile(made.source)).diagnostics, [], made.source);
    // Fisher's looks are summed exactly with calculate, not simulated.
    const exact = interimSource({outcome: 'binary', interimAdd: 'power'});
    assert.doesNotMatch(exact.source, /simulate\(/);
    assert.match(exact.source, /let power = calculate\(meets\(analysis=trial, target=target\)\)/);
    assert.deepEqual((await compile(exact.source)).diagnostics, [], exact.source);
  }
  // A t-test's size re-estimated at an interim look, its Type I judged at listed SDs.
  {
    const {studySource} = await import(new URL('designs.js', platform));
    const base = {outcome: 'continuous', control: 64, treatment: 64, test: 't_test', add: 'plan', seed: 7};
    assert.doesNotMatch(studySource(base).source, /blinded_reestimation/);
    const made = studySource({...base, reestimate: 'blinded', interimN: 30, maxN: 200});
    assert.match(made.source, /use designs\.adaptive/);
    assert.match(made.source, /blinded_reestimation\(analysis=analysis, interim_per_arm=30, difference=5, power=4\/5, max_per_arm=200\)/);
    assert.match(made.source, /null_scenarios\(at=\[mean_difference\(value=0, sd=6\), mean_difference\(value=0, sd=10\), mean_difference\(value=0, sd=14\)\]\)/);
    assert.match(made.source, /maximum_typeI=3\/40, nulls=nulls\)/);
    assert.deepEqual((await compile(made.source)).diagnostics, [], made.source);
    // Unequal arms are not re-estimated.
    assert.doesNotMatch(studySource({...base, treatment: 128, reestimate: 'blinded'}).source, /blinded_reestimation/);
  }
  // The family's power, simulated with its own procedure at one point per outcome.
  {
    const {severalSource} = await import(new URL('designs.js', platform));
    const endpoints = [{name: 'response', kind: 'binary'}, {name: 'symptoms', kind: 'continuous'}];
    for (const procedure of ['bonferroni', 'fixed_sequence', 'graphical']) {
      const plain = severalSource({procedure, endpoints}).source;
      assert.doesNotMatch(plain, /simulate\(/);
      const made = severalSource({procedure, endpoints, severalAdd: 'power', rejecting: 'all', seed: 7});
      assert.match(made.source, /endpoint_points\(at=\[binomial_rates\(p_control=3\/10, p_treatment=1\/2\), mean_difference\(value=5, sd=10\)\], correlation=1\/2\)/);
      assert.match(made.source, /rejecting="all"\)/);
      assert.deepEqual((await compile(made.source)).diagnostics, [], procedure + '\n' + made.source);
    }
  }
  // The prevalence survey card plans the prevalence for a margin of error.
  const {DESIGNS} = await import(new URL('designs.js', platform));
  const survey = DESIGNS.find(d => d.id === 'prevalence_survey');
  const planned = observationalSource({...survey.preset, exposure: 'smoking', outcome: 'asthma'});
  assert.match(planned.source, /planned_interval\(model=study, measure="prevalence"\)/);
  assert.match(planned.source, /precision_target\(at=proportion\(value=1\/10\), level=19\/20, margin_of_error=3\/100\)/);
  assert.deepEqual((await compile(planned.source)).diagnostics, [], planned.source);
  const clustered = observationalSource({...survey.preset, survey: 'cluster', clusters: 100, exposure: 'smoking', outcome: 'asthma'});
  assert.match(clustered.source, /method="normal"/);
  assert.match(clustered.source, /proportion\(value=1\/10, design_effect=2\)/);
  assert.deepEqual((await compile(clustered.source)).diagnostics, [], clustered.source);
  assert.match(observationalSource({design: 'case_control', add: 'precision', exposure: 'e', outcome: 'o'}).source,
    /relative_margin_of_error=1\/2\)[\s\S]*sample_size|relative_margin_of_error=1\/2\)/);
  for (const [state, pattern] of regressions) {
    const made = observationalSource({...state, plan: true, exposure: 'e', outcome: 'o'});
    assert.match(made.source, pattern, state.test + ' ' + state.design);
    assert.deepEqual((await compile(made.source)).diagnostics, [], made.source);
  }
  assert.match(observationalPlannable({...measured, test: 'linear_association', residualSd: '-1'}), /standard deviation/);
});

test('the wizard declares observational studies, and they read in words', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  const {observationalSource, studyName} = await import(new URL('wizard.js', platform));
  const compile = source => dispatch('/api/compile', {method: 'POST', body: JSON.stringify({source})}).json();

  // Every design the wizard offers compiles, with a proved test of association.
  for (const [design, population] of [['cohort', false], ['cohort', true], ['case_control', false], ['cross_sectional', false], ['matched_case_control', false]]) {
    const made = observationalSource({design, population, exposure: 'night shifts', outcome: 'insomnia', alpha: '1/40'});
    const result = await compile(made.source);
    assert.deepEqual(result.diagnostics, [], design + '\n' + made.source);
    assert.equal(made.evidence, 'proved');
    assert.equal(result.bindings.analysis.type, design === 'matched_case_control' ? 'MatchedAnalysis' : 'AssociationAnalysis');
    assert.match(result.bindings.study.reading, design.endsWith('case_control') ? /cases of insomnia/ : /night shifts/);
  }
  assert.ok(studyName('lung cancer') && !studyName('a"b') && !studyName(''));

  document.body.innerHTML = shell();
  await import(new URL('editor.js?observational', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !el('lesson').disabled && host.querySelector('.stack'), 'editor never loaded');
  await ready();
  el('newDoc').click();
  const wizard = document.querySelector('.wizard');
  const pick = (name, value) => {
    const input = wizard.querySelector('input[name="' + name + '"][value="' + value + '"]');
    input.checked = true;
    input.dispatchEvent(new window.Event('change', {bubbles: true}));
  };
  const preview = () => wizard.querySelector('.wizard-preview').textContent;
  pick('design', 'cohort');
  assert.deepEqual([...wizard.querySelectorAll('.wizard-crumb')].map(c => c.textContent.replace(/\d/g, '')), ['Design', 'Topic', 'Sampling', 'Test', 'Power', 'Name']);
  assert.match(preview(), /cohort\(exposed=100, unexposed=200, exposure="smoking", outcome="asthma"\)/);
  assert.match(wizard.querySelector('.wizard-verdict').textContent, /proved in Lean.*association, not an effect/);
  const population = wizard.querySelector('[data-part="population"]');
  pick('population', 'population');
  assert.match(preview(), /cohort\(n=400,/);
  pick('design', 'case_control');
  assert.match(preview(), /case_control\(cases=100, controls=200,/);
  assert.ok(population.hidden, 'only a cohort can be a population cohort');
  [...wizard.querySelectorAll('.wizard-crumb')].at(-1).click();
  wizard.querySelector('form').dispatchEvent(new window.Event('submit', {bubbles: true, cancelable: true}));
  await until(() => el('filename').textContent === 'my-study.stat', 'the wizard did not create a study');
  await ready();
  assert.equal(el('report').dataset.state, 'ready');
  assert.match(host.querySelector('.stack[data-name="study"] .stack-reading').textContent, /100 cases of asthma and 200 controls, asked about smoking/);
  assert.equal(host.querySelector('.stack[data-name="study"]').dataset.family, 'study');
  assert.ok([...document.querySelectorAll('.rail-item')].some(item => item.title === 'Observational studies'));
});

test('every design the language supports can be built from the wizard, and found by search', async t => {
  const window = new Window({url: 'http://localhost/'});
  const {document} = window;
  t.after(() => window.happyDOM.close());
  install(window);
  globalThis.fetch = async (url, options = {}) => dispatch(url, options);
  const D = await import(new URL('designs.js', platform));
  const compile = async source => (await dispatch('/api/compile', {method: 'POST', body: JSON.stringify({source})}).json())
    .diagnostics.filter(d => d.severity === 'error');

  // Every flow, with every test it offers and everything it can add, compiles.
  const built = [];
  for (const outcome of ['binary', 'continuous', 'repeated', 'survival']) {
    for (const question of ['differ', 'better', 'margin']) {
      if (!D.available(outcome, 'higher')[question]) continue;
      for (const unit of ['participants', 'clusters']) {
        const base = {outcome, question, unit, control: 60, treatment: 60, clustersControl: 6, clustersTreatment: 6, pTreatment: question === 'margin' ? '3/10' : '1/2'};
        for (const test of D.trialTests(base)) {
          const extras = D.trialExtras({...base, test});
          for (const add of ['none', ...(extras.plan ? ['plan'] : []), ...(extras.data ? ['data'] : [])]) {
            built.push(['trial ' + outcome + ' ' + question + ' ' + unit + ' ' + test + ' ' + add, D.studySource({...base, test, add, scheme: test === 'randomisation_test' ? 'stratified' : 'complete'})]);
          }
        }
      }
    }
  }
  for (const procedure of Object.keys(D.PROCEDURES)) {
    built.push(['several ' + procedure, D.severalSource({procedure, endpoints: [{name: 'response', kind: 'binary'}, {name: 'symptom score', kind: 'continuous'}, {name: 'relapse', kind: 'binary'}]})]);
  }
  for (const outcome of ['binary', 'continuous', 'survival']) built.push(['interim ' + outcome, D.interimSource({outcome})]);
  for (const add of ['none', 'plan', 'data']) built.push(['one arm ' + add, D.oneArmSource({add})]);
  built.push(['estimate', D.oneArmSource({aim: 'estimate'})], ['two stage', D.twoStageSource({})], ['two stage given', D.twoStageSource({find: 'given'})],
    ['estimate with a margin', D.oneArmSource({aim: 'estimate', add: 'precision'})],
    ['estimate with assurance', D.oneArmSource({aim: 'estimate', add: 'precision', marginKind: 'relative', moe: '1/3', assurance: '4/5'})],
    ['bayesian', D.twoStageSource({rule: 'posterior', find: 'given', n1: 10, n2: 20, alpha: '1/10'})]);
  for (const design of ['cohort', 'case_control', 'cross_sectional', 'matched_case_control', 'person_time']) {
    for (const [outcomeScale, exposureScale, survey] of [['binary', 'binary', 'simple_random'], ['continuous', 'continuous', 'simple_random'], ['binary', 'binary', 'weighted']]) {
      const base = {design, outcomeScale, exposureScale, survey, exposure: 'night shifts', outcome: 'insomnia'};
      for (const test of D.observedTests(base)) {
        const extras = D.observedExtras({...base, test});
        for (const add of ['none', ...(extras.plan ? ['plan'] : []), ...(extras.data ? ['data'] : []), ...(extras.precision ? ['precision'] : [])]) {
          built.push(['observed ' + design + ' ' + test + ' ' + add, D.observationalSource({...base, test, add})]);
        }
        // Every interval a design can plan for a margin of error compiles.
        for (const measure of Object.keys(D.precisionMeasures(base))) {
          built.push(['precision ' + design + ' ' + measure, D.observationalSource({...base, test, add: 'precision', precisionMeasure: measure})]);
        }
      }
    }
  }
  for (const [label, made] of built) assert.deepEqual(await compile(made.source), [], label + '\n' + made.source);
  // Every card leads somewhere, and every family has cards.
  for (const family of D.FAMILIES) assert.ok(D.DESIGNS.some(d => d.family === family.id), family.id);
  assert.ok(D.DESIGNS.every(d => D.FLOWS[d.flow]), 'every card has a flow');

  document.body.innerHTML = shell();
  await import(new URL('editor.js?designs', platform));
  const el = id => document.getElementById(id);
  const host = el('lessonBlocks');
  const ready = () => until(() => !host.inert && el('report').dataset.state !== 'pending', 'editor stayed busy');
  await until(() => !el('lesson').disabled && host.querySelector('.stack'), 'editor never loaded');
  await ready();
  const event = name => new window.Event(name, {bubbles: true, cancelable: true});

  // Search reaches a card in any family; Enter takes the first match.
  el('newDoc').click();
  let wizard = document.querySelector('.wizard');
  const step = () => wizard.querySelector('.wizard-step:not([hidden])').dataset.step;
  const visible = () => [...wizard.querySelectorAll('.wizard-designs .wizard-choice')].filter(c => !c.hidden).map(c => c.dataset.value);
  assert.deepEqual(visible(), D.DESIGNS.filter(d => d.family === 'trials').map(d => d.id), 'one family at a time');
  const search = wizard.querySelector('.wizard-search-input');
  // The chosen card is the one ticked, in every family: the radios hold the card itself.
  const ticked = () => [...wizard.querySelectorAll('.wizard-designs input:checked')].map(input => input.value);
  assert.deepEqual(ticked(), ['two_arm']);
  for (const id of ['non_inferiority', 'one_arm', 'regression', 'cohort', 'correlation']) {
    const input = wizard.querySelector('.wizard-designs input[value="' + id + '"]');
    input.checked = true;
    input.dispatchEvent(event('change'));
    assert.deepEqual(ticked(), [id], id);
  }
  search.value = 'cluster';
  search.dispatchEvent(event('input'));
  assert.deepEqual(visible(), ['cluster', 'survey']);
  wizard.querySelector('form').dispatchEvent(event('submit'));
  assert.equal(step(), 'outcome');
  assert.match(wizard.querySelector('.wizard-count').textContent, /Cluster-randomised/);
  const pick = (name, value) => {
    const input = wizard.querySelector('input[name="' + name + '"][value="' + value + '"]');
    input.checked = true;
    input.dispatchEvent(event('change'));
  };
  // The test step offers what fits whole clusters, the proved randomisation test among them.
  [...wizard.querySelectorAll('.wizard-crumb')][3].click();
  assert.equal(step(), 'test');
  assert.deepEqual([...wizard.querySelectorAll('input[name="test"]')].map(i => i.value), ['cluster_t_test', 'randomisation_test', 'declared_test']);
  pick('test', 'randomisation_test');
  pick('scheme', 'blocked');
  const blocks = wizard.querySelector('.wizard-pill[data-key="blockSize"]');
  blocks.value = '5';
  blocks.dispatchEvent(event('input'));
  // The compiler has the last word: blocks of 5 cannot split 12 clusters per arm, so Create holds.
  [...wizard.querySelectorAll('.wizard-crumb')].at(-1).click();
  const next = wizard.querySelector('.wizard-foot .btn.primary');
  await until(() => /cannot build this yet/.test(wizard.querySelector('.wizard-problem').textContent), 'the compile check never reported');
  assert.ok(next.disabled);
  blocks.value = '4';
  blocks.dispatchEvent(event('input'));
  await until(() => !next.disabled, 'a study that compiles can be created');
  assert.match(wizard.querySelector('.wizard-verdict').textContent, /proved in Lean/);
  wizard.querySelector('form').dispatchEvent(event('submit'));
  await until(() => el('filename').textContent === 'my-study.stat', 'the wizard did not create a study');
  await ready();
  assert.equal(el('report').dataset.state, 'ready');
  assert.match(el('source').value, /cluster_assignment\(clusters_control=12, clusters_treatment=12, n_control=50, n_treatment=50, randomisation="blocked", block_size=4\)/);

  // Every design is also a command: ⌘K and a word open the wizard on that design.
  document.dispatchEvent(new window.KeyboardEvent('keydown', {key: 'k', metaKey: true, bubbles: true}));
  const query = document.querySelector('.cmdk input');
  query.value = 'interim';
  query.dispatchEvent(event('input'));
  const row = [...document.querySelectorAll('.cmdk-item')].find(item => item.querySelector('.cmdk-label').textContent === 'Interim look');
  assert.ok(row, 'the palette lists the design');
  row.click();
  wizard = document.querySelector('.wizard');
  assert.equal(step(), 'outcome');
  assert.deepEqual([...wizard.querySelectorAll('.wizard-crumb')].map(c => c.textContent.replace(/\d/g, '')), ['Design', 'Outcome', 'Looks', 'Name']);
  wizard.querySelector('.wizard-close').click();

  // An empty study offers the families of designs.
  el('newDoc').click();
  [...document.querySelectorAll('.wizard button')].find(b => b.textContent === 'Start empty').click();
  await ready();
  const chips = [...host.querySelectorAll('.starter-family')];
  assert.equal(chips.length, D.FAMILIES.length);
  chips.find(c => /Observational/.test(c.textContent)).click();
  wizard = document.querySelector('.wizard');
  assert.deepEqual(visible(), D.DESIGNS.filter(d => d.family === 'observed').map(d => d.id));
  wizard.querySelector('.wizard-close').click();
});
