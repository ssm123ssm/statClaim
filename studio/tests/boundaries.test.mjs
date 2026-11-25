import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { boundaryLevels } from '../designs.js';

// The boundaries R's rpact and gsDesign give, pinned by replication/comparison/spending_boundaries_r.R.
const fixture = JSON.parse(readFileSync(new URL('../../tests/fixtures/spending_boundaries_r.json', import.meta.url), 'utf8'));

test('the studio computes the spending boundaries rpact and Python compute', () => {
  assert.ok(fixture.cases.length >= 4);
  for (const design of fixture.cases) {
    const information = design.sizes.map(([control, treatment]) => control * treatment / (control + treatment));
    const shares = information.map(info => info / information[information.length - 1]);
    const [numerator, denominator] = design.alpha.split('/').map(Number);
    const levels = boundaryLevels(shares, numerator / denominator, design.sides, design.spending);
    assert.equal(levels.length, design.nominal.length);
    levels.forEach((level, look) => {
      const gap = Math.abs(level - design.nominal[look]);
      assert.ok(gap < 1e-6, `${design.spending}, ${design.sides}-sided, look ${look + 1}: ${level} vs ${design.nominal[look]}`);
    });
  }
});
