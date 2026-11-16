import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import test from 'node:test';
import {
  auditSources,
  checkBuildWarnings,
  checkReplayOutput,
  discoverConfigs,
  replayPlan,
  runChecked,
} from './run-audits.mjs';

const standardAxioms = ['propext', 'Classical.choice', 'Quot.sound'];

function makeConfig(overrides = {}) {
  return {
    challenge_module: 'Pkg.Challenge',
    solution_module: 'Pkg.Solution',
    theorem_names: ['Pkg.claim'],
    permitted_axioms: standardAxioms,
    enable_nanoda: true,
    ...overrides,
  };
}

function tempDir(t, prefix = 'lpp-audit-test-') {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), prefix));
  t.after(() => fs.rmSync(dir, {recursive: true, force: true}));
  return dir;
}

function writeConfig(root, id, config) {
  const relative = path.join('comparator', id, 'comparator.json');
  const file = path.join(root, relative);
  fs.mkdirSync(path.dirname(file), {recursive: true});
  fs.writeFileSync(file, JSON.stringify(config));
  return relative;
}

function writeAuditSources(root, solutionText = '-- sorry and axiom in a comment\ntheorem ok : True := True.intro\n') {
  fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({name: 'LastPassagePercolation'}));
  fs.writeFileSync(path.join(root, 'lakefile.lean'), 'package LastPassagePercolation where\n');
  for (const mod of ['Pkg/Challenge', 'Pkg/Solution']) fs.mkdirSync(path.dirname(path.join(root, `${mod}.lean`)), {recursive: true});
  fs.writeFileSync(path.join(root, 'Pkg/Challenge.lean'), 'theorem claim : True := by sorry\n');
  fs.writeFileSync(path.join(root, 'Pkg/Solution.lean'), solutionText);
}

test('discoverConfigs rejects a root with no comparator configs', (t) => {
  const root = tempDir(t);
  fs.mkdirSync(path.join(root, 'comparator'));
  assert.throws(() => discoverConfigs(root), /No comparator configurations found/);
});

test('discoverConfigs rejects disabled Nanoda and malformed theorem names', (t) => {
  const root = tempDir(t);
  writeConfig(root, 'Disabled', makeConfig({enable_nanoda: false}));
  assert.throws(() => discoverConfigs(root), /Invalid configuration or disabled Nanoda/);

  fs.rmSync(path.join(root, 'comparator', 'Disabled'), {recursive: true});
  writeConfig(root, 'Malformed', makeConfig({theorem_names: ['not-qualified']}));
  assert.throws(() => discoverConfigs(root), /Invalid configuration or disabled Nanoda/);
});

test('replayPlan includes helper and Solution sources, excluding only configured Challenge modules', () => {
  const configs = [{data: makeConfig()}];
  const files = [
    'Pkg/Challenge.lean',
    'Pkg/Solution.lean',
    'Pkg/Helper.lean',
    'lakefile.lean',
  ];
  const plan = replayPlan(files, configs);
  assert.deepEqual(plan.challenges, ['Pkg.Challenge']);
  assert.deepEqual(plan.proofs, ['Pkg.Helper', 'Pkg.Solution']);
  assert.equal(plan.total, 3);
});

test('replayPlan rejects a configured Challenge whose source is missing', () => {
  assert.throws(() => replayPlan(['Pkg/Solution.lean'], [{data: makeConfig()}]), /Missing Challenge source/);
});

test('checkBuildWarnings allows only the configured Challenge sorry warning', () => {
  const root = path.resolve('/checkout');
  const configs = [{data: makeConfig()}];
  const allowed = 'warning: Pkg/Challenge.lean:12:3: declaration uses `sorry`';
  assert.equal(checkBuildWarnings(`${allowed}\n`, root, configs), 1);
  assert.throws(() => checkBuildWarnings('warning: Pkg/Solution.lean:12:3: declaration uses `sorry`', root, configs), /Unexpected build warning/);
  assert.throws(() => checkBuildWarnings('warning: Pkg/Solution.lean:2:4: unused variable', root, configs), /Unexpected build warning/);
});

test('checkReplayOutput rejects missing, duplicate, and unexpected replay progress', () => {
  const expected = ['Pkg.Helper', 'Pkg.Solution'];
  assert.doesNotThrow(() => checkReplayOutput('replaying Pkg.Helper\nreplaying Pkg.Solution\n', expected));
  assert.throws(() => checkReplayOutput('replaying Pkg.Helper\n', expected), /did not report replaying Pkg.Solution/);
  assert.throws(() => checkReplayOutput('replaying Pkg.Helper\nreplaying Pkg.Helper\nreplaying Pkg.Solution\n', expected), /duplicate replay/);
  assert.throws(() => checkReplayOutput('replaying Pkg.Helper\nreplaying Pkg.Solution\nreplaying Pkg.Other\n', expected), /Unexpected or duplicate replay/);
  assert.throws(() => checkReplayOutput('Lean kernel says OK\n', expected), /Unexpected kernel replay output/);
});

test('auditSources ignores comments but rejects proof holes and custom axioms outside Challenge', (t) => {
  const root = tempDir(t);
  const configs = [{data: makeConfig()}];
  const files = ['Pkg/Challenge.lean', 'Pkg/Solution.lean'];
  writeAuditSources(root);
  assert.doesNotThrow(() => auditSources(root, files, configs));

  fs.writeFileSync(path.join(root, 'Pkg/Solution.lean'), 'theorem unfinished : True := by sorry\n');
  assert.throws(() => auditSources(root, files, configs), /forbidden proof hole/);
  fs.writeFileSync(path.join(root, 'Pkg/Solution.lean'), 'axiom custom : True\n');
  assert.throws(() => auditSources(root, files, configs), /forbidden proof hole, axiom or native escape/);
});

test('runChecked rejects success-looking output with nonzero exit and records the failure', async (t) => {
  const output = tempDir(t);
  await assert.rejects(
    runChecked({name: 'exit-seven', command: process.execPath, args: ['-e', "console.log('all checks passed'); process.exit(7)"], cwd: process.cwd(), output, quiet: true}),
    error => {
      assert.equal(error.record.exit_code, 7);
      assert.equal(error.record.timed_out, false);
      assert.match(fs.readFileSync(error.record.log, 'utf8'), /all checks passed/);
      return true;
    },
  );
});

test('runChecked records a missing executable as failure', async (t) => {
  const output = tempDir(t);
  await assert.rejects(
    runChecked({name: 'missing-executable', command: path.join(output, 'does-not-exist'), args: [], cwd: process.cwd(), output, quiet: true}),
    error => {
      assert.ok(error.record.error);
      assert.equal(error.record.exit_code === 0, false);
      return true;
    },
  );
});

test('runChecked records a successful child exit', async (t) => {
  const output = tempDir(t);
  const record = await runChecked({name: 'success', command: process.execPath, args: ['-e', "console.log('ok')"], cwd: process.cwd(), output, quiet: true});
  assert.equal(record.exit_code, 0);
  assert.equal(record.timed_out, false);
  assert.match(fs.readFileSync(record.log, 'utf8'), /ok/);
});
