#!/usr/bin/env node
// Compares the elaborated statements of the Challenge and the Solution theorems, from two probe logs.
//
// The text check (check-challenges.mjs) shows the two files say the same thing in the same words. This script shows
// that the words elaborate to the same terms in both modules (an import of the Solution could add a notation or a
// global instance that the Challenge does not see).
//
// Step 1: create a temporary directory and write the two probe files:
//   probe_dir=$(mktemp -d)
//   node scripts/compare-challenge-types.mjs probe comparator/<P>/comparator.json challenge "$probe_dir/challenge.lean"
//   node scripts/compare-challenge-types.mjs probe comparator/<P>/comparator.json solution "$probe_dir/solution.lean"
// Step 2: compile each probe separately with `lake env lean`, keeping both complete output logs. Each probe imports
//   only its own module, since the two modules declare the same names.
// Step 3: compare the logs:
//   node scripts/compare-challenge-types.mjs compare comparator/<P>/comparator.json <challenge log> <solution log>
//
// `compare` checks, for every theorem named in comparator.json, that the printed `pp.all` type is identical in the
// two logs, that the Solution theorem depends on exactly propext, Classical.choice, Quot.sound, and that the Challenge
// theorem depends on those plus sorryAx. It prints one line per theorem and exits 1 on any difference.
// Comparison ignores layout whitespace outside literals and the optional leading @ on the checked theorem header.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const STANDARD = ['propext', 'Classical.choice', 'Quot.sound'];

function readConfig(configPath) {
  const data = JSON.parse(fs.readFileSync(configPath, 'utf8'));
  const name = /^[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+$/;
  if (!data || typeof data !== 'object' ||
      !Array.isArray(data.theorem_names) || data.theorem_names.length === 0 ||
      !data.theorem_names.every((n) => typeof n === 'string' && name.test(n)) ||
      new Set(data.theorem_names).size !== data.theorem_names.length) throw Error('theorem_names must be unique qualified names');
  for (const key of ['challenge_module', 'solution_module']) {
    if (typeof data[key] !== 'string' || !name.test(data[key])) throw Error(`${key} must be a qualified module name`);
  }
  if (!Array.isArray(data.permitted_axioms) ||
      JSON.stringify([...data.permitted_axioms].sort()) !== JSON.stringify([...STANDARD].sort()) ||
      data.enable_nanoda !== true) throw Error('expected the standard three permitted axioms and enable_nanoda: true');
  return data;
}

function probeText(data, which) {
  const mod = which === 'challenge' ? data.challenge_module : data.solution_module;
  if (!mod) throw Error(`${which}_module missing`);
  const lines = [`import ${mod}`];
  for (const n of data.theorem_names) {
    lines.push('set_option pp.maxSteps 10000000 in', 'set_option pp.all true in', `#check @${n}`);
  }
  for (const n of data.theorem_names) lines.push(`#print axioms ${n}`);
  return lines.join('\n') + '\n';
}

// Canonicalize layout only. Whitespace inside strings and quoted identifiers remains significant.
function normalizeLayout(text) {
  const literal = /r(#+)?"[\s\S]*?"\1|"(?:\\.|[^"\\])*"|«[^»]*»|'(?:\\.|[^\\'\n])'/g;
  let result = ''; let end = 0;
  for (const match of text.matchAll(literal)) {
    result += text.slice(end, match.index).replace(/\s+/g, ' ') + match[0];
    end = match.index + match[0].length;
  }
  return (result + text.slice(end).replace(/\s+/g, ' ')).trim();
}

/** Read complete #check records and bracketed #print axioms records from raw Lean output. */
export function parseLog(text) {
  const types = new Map(); const axioms = new Map(); const errors = [];
  const lines = text.split('\n');
  let current = null;
  const finishType = () => {
    if (!current) return;
    const raw = current.lines.join('\n');
    const header = /^@?([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)(?:\.\{[^}]*\})?\s*:\s*([\s\S]+)$/.exec(raw);
    if (!header || !header[2].trim() || /\.\.\.|⋯|<truncated>/.test(raw)) errors.push(`incomplete or truncated type for ${current.name}`);
    else if (types.has(current.name)) errors.push(`duplicate printed type for ${current.name}`);
    else types.set(current.name, normalizeLayout(raw.replace(/^@/, '')));
    current = null;
  };
  const storeAxioms = (name, list) => {
    if (axioms.has(name)) errors.push(`duplicate axiom record for ${name}`);
    else if (new Set(list).size !== list.length) errors.push(`duplicate axiom in record for ${name}`);
    else axioms.set(name, list);
  };
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^\s*(?:.*:\d+:\d+:\s*)?(?:error|panic):/.test(line) ||
        /"terminal_exit"\s*:\s*(?!0\b)-?\d+/.test(line)) {
      finishType(); errors.push('probe log contains an error or nonzero exit'); continue;
    }
    const ax = /^'([^']+)' depends on axioms:\s*\[/.exec(line);
    if (ax) {
      finishType();
      let record = line.slice(ax[0].length);
      while (!record.includes(']') && i + 1 < lines.length) record += '\n' + lines[++i];
      if (!/^[\s\w.,]*\]\s*$/.test(record)) errors.push(`incomplete or malformed axiom record for ${ax[1]}`);
      else {
        const content = record.slice(0, record.indexOf(']')).trim();
        const list = content ? content.split(',').map((s) => s.trim()) : [];
        if (list.some((a) => !/^[A-Za-z_][A-Za-z0-9_.]*$/.test(a))) errors.push(`malformed axiom list for ${ax[1]}`);
        else storeAxioms(ax[1], list);
      }
      continue;
    }
    const none = /^'([^']+)' does not depend on any axioms\s*$/.exec(line);
    if (none) { finishType(); storeAxioms(none[1], []); continue; }
    const start = /^@?([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)(?=\.\{|\s*:)/.exec(line);
    if (start) { finishType(); current = { name: start[1], lines: [line] }; continue; }
    if (current && /^\s+\S/.test(line)) current.lines.push(line);
    else if (current && line.trim()) {
      finishType();
      if (!/^\{/.test(line) && !/error:|warning:/.test(line)) errors.push(`unexpected line after printed type: ${line.slice(0, 80)}`);
    }
  }
  finishType();
  return { types, axioms, errors };
}

// universe names in a printed type are not part of the statement's content (`u_1` against `u`); keep them as printed,
// because both modules name them the same way when the text is the same.
export function compareLogs(data, challengeLog, solutionLog) {
  const ch = parseLog(challengeLog); const so = parseLog(solutionLog);
  const results = [];
  for (const n of data.theorem_names) {
    const errors = [];
    errors.push(...ch.errors.map((e) => `challenge: ${e}`), ...so.errors.map((e) => `solution: ${e}`));
    const ct = ch.types.get(n); const st = so.types.get(n);
    if (ct === undefined) errors.push('no printed type in the challenge log');
    if (st === undefined) errors.push('no printed type in the solution log');
    if (ct !== undefined && st !== undefined && ct !== st) errors.push('the printed types differ');
    const ca = ch.axioms.get(n); const sa = so.axioms.get(n);
    if (sa === undefined) errors.push('no axiom line in the solution log');
    else if (JSON.stringify([...sa].sort()) !== JSON.stringify([...STANDARD].sort())) errors.push(`solution axioms [${sa.join(', ')}]`);
    if (ca === undefined) errors.push('no axiom line in the challenge log');
    else if (JSON.stringify([...ca].sort()) !== JSON.stringify([...STANDARD, 'sorryAx'].sort())) errors.push(`challenge axioms [${ca.join(', ')}]`);
    results.push({ name: n, errors, length: ct?.length ?? 0 });
  }
  return results;
}

function main() {
  const [mode, configPath, ...rest] = process.argv.slice(2);
  if (mode === 'probe' && configPath && rest.length === 2 && ['challenge', 'solution'].includes(rest[0])) {
    const out = path.resolve(rest[1]);
    fs.writeFileSync(out, probeText(readConfig(configPath), rest[0]));
    console.log(`wrote ${out}`);
    return 0;
  }
  if (mode === 'compare' && configPath && rest.length === 2) {
    const data = readConfig(configPath);
    const results = compareLogs(data, fs.readFileSync(rest[0], 'utf8'), fs.readFileSync(rest[1], 'utf8'));
    let failed = false;
    for (const r of results) {
      if (r.errors.length) { failed = true; console.log(`FAIL ${r.name}: ${r.errors.join('; ')}`); }
      else console.log(`IDENTICAL ${r.name} (${r.length} normalized characters; solution axioms standard, challenge axioms standard plus sorryAx)`);
    }
    return failed ? 1 : 0;
  }
  console.log('usage:\n  node scripts/compare-challenge-types.mjs probe <comparator.json> challenge|solution <out.lean>\n  node scripts/compare-challenge-types.mjs compare <comparator.json> <challenge log> <solution log>');
  return 2;
}

if (process.argv[1] && fs.realpathSync(process.argv[1]) === fs.realpathSync(fileURLToPath(import.meta.url))) process.exitCode = main();
