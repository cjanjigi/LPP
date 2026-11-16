#!/usr/bin/env node
// Build, statement/axiom comparison, kernel replay and the isolated Lean/Nanoda comparator.
// All verification commands use the project's pinned Lake environment. No checker fallback is allowed.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawn, spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {maskCode} from './check-challenges.mjs';

const script = fileURLToPath(import.meta.url);
const ROOT = path.resolve(path.dirname(script), '..');
const STANDARD = ['Classical.choice', 'Quot.sound', 'propext'];
const NAME = /^[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+$/;
const FLAGS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
  '-Dlinter.unusedVariables=true', '-Dlinter.unusedSectionVars=true',
  '-Dlinter.unusedSimpArgs=true', '-Dlinter.unnecessarySimpa=true', '-Dlinter.deprecated=true'];

export function discoverConfigs(root) {
  const dir = path.join(root, 'comparator');
  const configs = fs.readdirSync(dir, {withFileTypes: true}).filter(e => e.isDirectory())
    .map(e => ({id: e.name, relative: `comparator/${e.name}/comparator.json`}))
    .filter(c => fs.existsSync(path.join(root, c.relative)))
    .sort((a, b) => a.id.localeCompare(b.id));
  if (!configs.length) throw Error('No comparator configurations found');
  for (const cfg of configs) {
    cfg.data = JSON.parse(fs.readFileSync(path.join(root, cfg.relative), 'utf8'));
    const d = cfg.data;
    if (!NAME.test(d.challenge_module) || !NAME.test(d.solution_module) ||
        !Array.isArray(d.theorem_names) || !d.theorem_names.length ||
        !d.theorem_names.every(n => typeof n === 'string' && NAME.test(n)) ||
        new Set(d.theorem_names).size !== d.theorem_names.length ||
        !Array.isArray(d.permitted_axioms) ||
        JSON.stringify([...d.permitted_axioms].sort()) !== JSON.stringify(STANDARD) || d.enable_nanoda !== true) {
      throw Error(`Invalid configuration or disabled Nanoda: ${cfg.relative}`);
    }
  }
  return configs;
}

export function replayPlan(files, configs) {
  const modules = files.filter(f => f.endsWith('.lean') && f !== 'lakefile.lean')
    .map(f => f.slice(0, -5).replaceAll('/', '.')).sort();
  if (!modules.length) throw Error('No tracked Lean modules found');
  const challenges = [...new Set(configs.map(c => c.data.challenge_module))].sort();
  for (const c of challenges) if (!modules.includes(c)) throw Error(`Missing Challenge source: ${c}`);
  const proofs = modules.filter(m => !challenges.includes(m));
  if (!proofs.length) throw Error('No proof modules to replay');
  // Challenge/Solution modules deliberately redeclare the same names, so replay Challenges separately.
  return {proofs, challenges, total: modules.length};
}

export function auditSources(root, files, configs) {
  const manifest = JSON.parse(fs.readFileSync(path.join(root, 'lake-manifest.json'), 'utf8'));
  const lakefile = fs.readFileSync(path.join(root, 'lakefile.lean'), 'utf8');
  if (manifest.name !== 'LastPassagePercolation' ||
      !/^package\s+(?:LastPassagePercolation|«LastPassagePercolation»)\s+where\s*$/m.test(lakefile)) {
    throw Error('Release package identity must remain LastPassagePercolation in both Lake metadata files');
  }
  const challenges = new Set(configs.map(c => `${c.data.challenge_module.replaceAll('.', '/')}.lean`));
  for (const f of files) {
    if (!f.endsWith('.lean') || f === 'lakefile.lean') continue;
    if (f.split('/').some(p => p === 'reference' || p === 'references')) throw Error(`Reference code in release: ${f}`);
    if (fs.lstatSync(path.join(root, f)).isSymbolicLink()) throw Error(`Lean source must be a regular release file: ${f}`);
    const {masked, lexicalErrors} = maskCode(fs.readFileSync(path.join(root, f), 'utf8'));
    if (lexicalErrors.length) throw Error(`${f}: ${lexicalErrors.join('; ')}`);
    if (challenges.has(f)) continue; // check-challenges.mjs validates the precise permitted holes.
    const forbidden = /\b(?:sorry|sorryAx|admit|axiom|native_decide)\b|\bLean\.ofReduceBool\b/.exec(masked);
    if (forbidden) throw Error(`${f}: forbidden proof hole, axiom or native escape (${forbidden[0]})`);
  }
}

export function checkBuildWarnings(text, root, configs) {
  const allowed = new Set(configs.map(c => `${c.data.challenge_module.replaceAll('.', '/')}.lean`));
  let intentional = 0;
  for (const line of text.split('\n')) {
    if (!/\bwarning:/i.test(line)) continue;
    const m = /^warning: (.+?):\d+:\d+: declaration uses `sorry`\s*$/.exec(line);
    const file = m && path.relative(root, path.resolve(root, m[1])).replaceAll(path.sep, '/');
    if (!m || !allowed.has(file)) throw Error(`Unexpected build warning: ${line}`);
    intentional++;
  }
  return intentional;
}

export function checkReplayOutput(text, expected) {
  const lines = text.split('\n').map(x => x.trim()).filter(Boolean);
  const seen = new Set();
  for (const line of lines) {
    if (!line.startsWith('replaying ')) throw Error(`Unexpected kernel replay output: ${line}`);
    const name = line.slice('replaying '.length);
    if (!expected.includes(name) || seen.has(name)) throw Error(`Unexpected or duplicate replay: ${name}`);
    seen.add(name);
  }
  for (const name of expected) if (!seen.has(name)) throw Error(`Kernel did not report replaying ${name}`);
}

export async function runChecked({name, command, args, cwd, output, timeoutMs = 90 * 60 * 1000, quiet = false}) {
  fs.mkdirSync(output, {recursive: true});
  const log = path.join(output, `${name}.log`);
  const fd = fs.openSync(log, 'w');
  const started = Date.now();
  if (!quiet) console.log(`\n== ${name} ==`);
  return await new Promise((resolve, reject) => {
    let timedOut = false;
    let startError;
    const child = spawn(command, args, {
      cwd, env: process.env, detached: process.platform !== 'win32', stdio: ['ignore', 'pipe', 'pipe']
    });
    const terminate = signal => {
      if (!child.pid) return;
      try { process.kill(process.platform === 'win32' ? child.pid : -child.pid, signal); }
      catch (e) { if (e.code !== 'ESRCH') throw e; }
    };
    let killTimer;
    const timer = setTimeout(() => {
      timedOut = true;
      terminate('SIGTERM');
      killTimer = setTimeout(() => terminate('SIGKILL'), 30000);
    }, timeoutMs);
    const stream = bytes => { fs.writeSync(fd, bytes); if (!quiet) process.stdout.write(bytes); };
    child.stdout.on('data', stream);
    child.stderr.on('data', stream);
    child.on('error', e => { startError = String(e); });
    child.on('close', (exitCode, signal) => {
      clearTimeout(timer);
      clearTimeout(killTimer);
      fs.closeSync(fd);
      const record = {name, command, args, exit_code: exitCode, signal, timed_out: timedOut,
        milliseconds: Date.now() - started, log, ...(startError ? {error: startError} : {})};
      if (exitCode === 0 && !timedOut && !startError) resolve(record);
      else reject(Object.assign(Error(`${name} failed (exit ${exitCode}${signal ? `, ${signal}` : ''}); ${log}`), {record}));
    });
  });
}

function trackedFiles(root) {
  const r = spawnSync('git', ['ls-files', '-z', '--', '*.lean'], {cwd: root, encoding: 'utf8'});
  if (r.status !== 0) throw Error(`Cannot inventory tracked Lean files: ${r.stderr}`);
  return r.stdout.split('\0').filter(Boolean);
}

export async function main(args) {
  let stage = 'all';
  let output;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--stage' && args[i + 1]) stage = args[++i];
    else if (args[i] === '--output' && args[i + 1]) output = path.resolve(args[++i]);
    else throw Error(`Usage: node scripts/run-audits.mjs [--stage guards|build|types|replay|comparator] [--output DIR]`);
  }
  const stages = ['guards', 'build', 'types', 'replay', 'comparator'];
  if (stage !== 'all' && !stages.includes(stage)) throw Error(`Unknown audit stage: ${stage}`);
  if ((stage === 'all' || stage === 'comparator') && process.platform !== 'linux') {
    throw Error('The full comparator requires Linux and bubblewrap. Run it in GitHub CI; no isolation bypass is used.');
  }
  output ??= fs.mkdtempSync(path.join(os.tmpdir(), 'last-passage-percolation-audits-'));
  const dir = path.join(output, stage);
  fs.mkdirSync(dir, {recursive: true});
  const report = {stage, started: new Date().toISOString(), status: 'running', checks: []};
  const save = () => fs.writeFileSync(path.join(dir, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  const run = async (name, command, argv, timeoutMs) => {
    try {
      const result = await runChecked({name, command, args: argv, cwd: ROOT, output: dir, timeoutMs});
      report.checks.push(result);
      return result.log;
    } catch (error) {
      if (error.record) report.checks.push(error.record);
      throw error;
    } finally { save(); }
  };
  save();
  try {
    const configs = discoverConfigs(ROOT);
    const files = trackedFiles(ROOT);
    report.configurations = configs.map(c => ({name: c.id, theorems: c.data.theorem_names.length}));
    auditSources(ROOT, files, configs);
    for (const current of stage === 'all' ? stages : [stage]) {
      if (current === 'guards') {
        await run('structural-check', process.execPath, ['scripts/check-challenges.mjs']);
      } else if (current === 'build') {
        const log = await run('build', 'lake', ['build']);
        report.intentional_challenge_warnings = checkBuildWarnings(fs.readFileSync(log, 'utf8'), ROOT, configs);
      } else if (current === 'types') {
        for (const cfg of configs) {
          for (const side of ['challenge', 'solution']) {
            const probe = path.join(dir, `${cfg.id}-${side}.lean`);
            await run(`${cfg.id}-${side}-generate`, process.execPath,
              ['scripts/compare-challenge-types.mjs', 'probe', cfg.relative, side, probe]);
            await run(`${cfg.id}-${side}`, 'lake', ['env', 'lean', ...FLAGS, probe]);
          }
          await run(`${cfg.id}-compare`, process.execPath, ['scripts/compare-challenge-types.mjs', 'compare', cfg.relative,
            path.join(dir, `${cfg.id}-challenge.log`), path.join(dir, `${cfg.id}-solution.log`)]);
        }
      } else if (current === 'replay') {
        const plan = replayPlan(files, configs);
        for (const mod of [...plan.proofs, ...plan.challenges]) {
          if (!fs.existsSync(path.join(ROOT, '.lake/build/lib/lean', `${mod.replaceAll('.', '/')}.olean`))) {
            throw Error(`Kernel replay requires a completed build; missing ${mod}`);
          }
        }
        const aggregate = 'LastPassagePercolationAuditReplay';
        if (plan.proofs.includes(aggregate)) throw Error(`Reserved temporary module already exists: ${aggregate}`);
        const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'last-passage-percolation-replay-'));
        const source = path.join(temp, `${aggregate}.lean`);
        fs.writeFileSync(source, plan.proofs.map(m => `import ${m}`).join('\n') + '\n');
        await run('replay-compile', 'lake', ['env', 'lean', '-R', temp, '-o',
          path.join(ROOT, '.lake/build/lib/lean', `${aggregate}.olean`), source]);
        const fresh = await run('replay-fresh', 'lake', ['env', 'leanchecker', '--verbose', '--fresh', aggregate]);
        checkReplayOutput(fs.readFileSync(fresh, 'utf8'), [`${aggregate} with --fresh`]);
        for (let i = 0; i < plan.challenges.length; i++) {
          const mod = plan.challenges[i];
          const log = await run(`replay-challenge-${i + 1}`, 'lake', ['env', 'leanchecker', '--verbose', mod]);
          checkReplayOutput(fs.readFileSync(log, 'utf8'), [mod]);
        }
        report.kernel_replay = {proof_modules_in_fresh_environment: plan.proofs.length,
          challenge_modules_replayed_separately: plan.challenges.length, total_project_modules: plan.total};
      } else if (current === 'comparator') {
        for (const cfg of configs) {
          // enable_nanoda:true is mandatory and is acted on by the pinned bundled comparator.
          await run(`${cfg.id}-comparator`, 'lake', ['comparator', '--config', cfg.relative]);
        }
        report.comparator_audits = configs.length;
      }
    }
    report.status = 'passed';
    console.log(`\n${stage}: passed; logs: ${dir}`);
  } catch (error) {
    report.status = 'failed';
    report.error = String(error);
    throw error;
  } finally {
    report.finished = new Date().toISOString();
    save();
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === script) {
  main(process.argv.slice(2)).catch(error => { console.error(error.message); process.exitCode = 1; });
}
