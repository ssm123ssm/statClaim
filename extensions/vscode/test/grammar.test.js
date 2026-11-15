const assert = require('node:assert/strict');
const test = require('node:test');
const grammar = require('../syntaxes/statproof.tmLanguage.json');

test('highlighting recognizes keywords, operations, constructors, arguments, and exact numbers', () => {
  function recognizes(scope, text) {
    const pattern = grammar.patterns.find(item => item.name.startsWith(scope));
    return new RegExp(pattern.match).test(text);
  }
  assert.ok(recognizes('keyword.control', 'let claim = typeI(analysis)'));
  assert.ok(!recognizes('keyword.control', 'letter'));
  assert.ok(recognizes('support.function', 'verify(claim)'));
  assert.ok(recognizes('entity.name.function', 'fisher('));
  assert.ok(recognizes('variable.parameter', 'alpha=0.05'));
  assert.ok(recognizes('constant.numeric', '0.05'));
  assert.ok(recognizes('constant.numeric', '1 / 20'));
  assert.ok(recognizes('comment.line', '# comment'));
});

test('strings highlight JSON escapes', () => {
  const string = grammar.patterns.find(item => item.name.startsWith('string.'));
  assert.equal(string.begin, '"');
  assert.equal(string.end, '"');
  assert.ok(new RegExp(string.patterns[0].match).test('\\"'));
});
