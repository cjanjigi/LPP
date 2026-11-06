#!/usr/bin/env node
// Checks the Challenge/Solution correspondence of every comparator configuration.
//
// For each comparator/<Project>/comparator.json this script checks that
//   - the configuration is well formed (module names, theorem names, the three standard axioms, nanoda on);
//   - the Challenge module imports only Mathlib, has no private or unexported declaration, no sorry except in the
//     named theorems, and is at most 1000 lines and 100 KiB (a warning above 300 lines or 32 KiB);
//   - the Solution module does not import the Challenge module, has no private or unexported declaration and no
//     sorry, admit, axiom or native_decide;
//   - each named theorem is declared in both modules, and its Challenge proof is `sorry`;
//   - every declaration of the Challenge (definitions, structures, theorems) appears in the Solution with the same
//     text, character for character, except that the Challenge's `sorry` proof is replaced by a proof;
//   - the Solution adds only theorems and lemmas, and no declaration of the Challenge sees a different
//     `namespace`, `open`, `variable`, `universe` or `section` setup in the Solution.
//
// Usage: node scripts/check-challenges.mjs [--root DIR]
// Prints one PASS or FAIL line per project (with its reasons) and exits with status 1 if any project fails.
// This is a text check. It does not compile anything; the build and the axiom probe do that.
// The accepted file grammar is deliberately restricted; unsupported commands fail, including trailing commands.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const STANDARD_AXIOMS = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const CHALLENGE_MAX_LINES = 1000;
const CHALLENGE_MAX_BYTES = 100 * 1024;
const CHALLENGE_REVIEW_LINES = 300;
const CHALLENGE_REVIEW_BYTES = 32 * 1024;

const IDENT = String.raw`(?:[A-Za-z_][A-Za-z0-9_'!?]*|«[^»\n]+»)`;
const NAME = String.raw`${IDENT}(?:\.${IDENT})*`;
const IMPORT = /^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)[ \t]*$/;
const NAMESPACE = new RegExp(String.raw`^[ \t]*namespace[ \t]+(${NAME})[ \t]*$`);
const SECTION = new RegExp(
  String.raw`^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*((?:(?:public|private|noncomputable)[ \t]+)*)section(?:[ \t]+${NAME})?[ \t]*$`);
const END = new RegExp(String.raw`^[ \t]*end(?:[ \t]+${NAME})?[ \t]*$`);
const DECL = new RegExp(
  String.raw`^[ \t]*(?:(?:open|set_option)\b[^\n]*?\bin[ \t]+)*(?:@\[[^\]\n]*\][ \t]*)*` +
  String.raw`((?:(?:private|protected|public|meta|noncomputable|unsafe|partial|nonrec|scoped|local)[ \t]+)*)` +
  String.raw`(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|axiom)\b` +
  String.raw`(?:[ \t]+(${NAME}))?`);
const PREFIX_LINE = /^(?:@\[[^\]\n]*\][ \t]*|(?:open|set_option)\b.*\bin[ \t]*)$/;
const CHAR_LITERAL = /^'(?:\\.|[^\\'\n])'/;
const OPEN = new RegExp(String.raw`^[ \t]*open[ \t]+(?:scoped[ \t]+)?${NAME}(?:[ \t]+${NAME})*[ \t]*$`);
const UNIVERSE = new RegExp(String.raw`^[ \t]*universe[ \t]+${IDENT}(?:[ \t]+${IDENT})*[ \t]*$`);
const APPROVED_MODIFIERS = new Set(['public', 'protected', 'noncomputable']);
const APPROVED_DECLARATIONS = new Set(['theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'inductive']);
const CONFIG_NAME = /^[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+$/;

/** Blank comments and string literals, keeping offsets and newlines. Also returns the comment spans. */
export function maskCode(text) {
  const out = text.split('');
  const comments = [];
  const lexicalErrors = [];
  const blank = (s, e) => { for (let k = s; k < e; k++) if (out[k] !== '\n') out[k] = ' '; };
  let i = 0;
  const n = text.length;
  while (i < n) {
    if (text[i] === '«') {
      // a quoted identifier: its text cannot start a comment or a string
      const e = text.indexOf('»', i);
      if (e < 0) lexicalErrors.push('unclosed quoted identifier');
      i = e < 0 ? n : e + 1;
    } else if (/^r#*"/.test(text.slice(i, i + 10)) && !(i > 0 && /[A-Za-z0-9_'!?]/.test(text[i - 1]))) {
      // a raw string literal r"...", r#"..."#
      const hashes = /^r(#*)"/.exec(text.slice(i, i + 10))[1];
      const close = '"' + hashes;
      const e = text.indexOf(close, i + hashes.length + 2);
      if (e < 0) lexicalErrors.push('unclosed raw string');
      const end = e < 0 ? n : e + close.length;
      blank(i, end); i = end;
    } else if (text.startsWith('--', i)) {
      let e = text.indexOf('\n', i); if (e < 0) e = n;
      comments.push({ start: i, end: e, doc: false }); blank(i, e); i = e;
    } else if (text.startsWith('/-', i)) {
      const start = i; let depth = 1; i += 2;
      while (i < n && depth) {
        if (text.startsWith('/-', i)) { depth++; i += 2; }
        else if (text.startsWith('-/', i)) { depth--; i += 2; }
        else i++;
      }
      if (depth) lexicalErrors.push('unclosed block comment');
      comments.push({ start, end: i, doc: text.startsWith('/--', start) }); blank(start, i);
    } else if (text[i] === "'" && CHAR_LITERAL.test(text.slice(i, i + 12)) &&
               !(i > 0 && /[A-Za-z0-9_'!?]/.test(text[i - 1]))) {
      i += CHAR_LITERAL.exec(text.slice(i, i + 12))[0].length;
    } else if (text[i] === '"') {
      const start = i; i++;
      while (i < n && text[i] !== '"') i += text[i] === '\\' ? 2 : 1;
      if (i >= n) lexicalErrors.push('unclosed string');
      i = Math.min(i + 1, n); blank(start, i);
    } else i++;
  }
  return { masked: out.join(''), comments, lexicalErrors };
}

function qualifiedName(namespaces, name) {
  return name.startsWith('_root_.') ? name.slice(7) : [...namespaces, name].join('.');
}

/**
 * Splits a module into imports and blocks. A block is one top-level command with its doc comment, attributes and
 * `open ... in` prefixes. Each block has kind `decl` (with `declKind`, `name`, `modifiers`, `exported`) or
 * `context` (namespace, end, section, open, universe) or `unsupported` for any other command.
 */
export function parseModule(text) {
  const { masked, comments, lexicalErrors } = maskCode(text);
  const lineStarts = [0];
  for (let k = 0; k < text.length; k++) if (text[k] === '\n') lineStarts.push(k + 1);
  const lineEnd = (l) => (l + 1 < lineStarts.length ? lineStarts[l + 1] - 1 : text.length);
  // every import token of the masked text, wherever it stands, and every line that is not exactly one import
  const imports = [];
  const badImportLines = [];
  for (const mline of masked.split('\n')) {
    if (!/\bimport\b/.test(mline)) continue;
    const tokens = [...mline.matchAll(/(?:^|\s)import[ \t]+(?:all[ \t]+)?(\S+)/g)].map((x) => x[1]);
    imports.push(...tokens);
    if (!IMPORT.test(mline)) badImportLines.push(mline.trim());
  }
  const items = []; // {start, kind: 'doc' | 'code', line}
  const docStarts = new Map(comments.filter((c) => c.doc).map((c) => [c.start, c]));
  for (let l = 0; l < lineStarts.length; l++) {
    const s = lineStarts[l];
    const mline = masked.slice(s, lineEnd(l));
    if (docStarts.has(s)) items.push({ start: s, kind: 'doc', line: l });
    else if (/^\S/.test(mline)) items.push({ start: s, kind: 'code', line: l, mtext: mline.trimEnd() });
  }
  const blocks = [];
  const grammarErrors = lexicalErrors.slice();
  let headerOpen = true;
  let sawModule = false;
  let pendingStart = null;
  for (const it of items) {
    if (it.kind === 'doc') { if (pendingStart === null) pendingStart = it.start; continue; }
    if (it.mtext === 'module') {
      if (sawModule || !headerOpen) grammarErrors.push('module must occur exactly once in the header');
      sawModule = true; pendingStart = null; continue;
    }
    if (/^(?:public[ \t]+)?(?:meta[ \t]+)?import\b/.test(it.mtext)) {
      if (!sawModule || !headerOpen) grammarErrors.push('imports must occur after module and before any other command');
      pendingStart = null; continue;
    }
    headerOpen = false;
    if (PREFIX_LINE.test(it.mtext)) { if (pendingStart === null) pendingStart = it.start; continue; }
    blocks.push({ start: pendingStart ?? it.start, firstLine: it.mtext });
    pendingStart = null;
  }
  if (pendingStart !== null && masked.slice(pendingStart).trim()) grammarErrors.push('trailing attribute or command prefix without a declaration');
  // block ends: just after the last line with code before the next block start
  for (let b = 0; b < blocks.length; b++) {
    const limit = b + 1 < blocks.length ? blocks[b + 1].start : text.length;
    let end = limit;
    while (end > blocks[b].start && /^\s*$/.test(masked.slice(end - 1, end))) end--;
    // end now points after the last non-space masked character before `limit`; move to the end of that line
    const ln = text.indexOf('\n', end);
    end = ln < 0 || ln > limit ? Math.min(limit, text.length) : ln;
    blocks[b].end = end;
    blocks[b].text = text.slice(blocks[b].start, end).trimEnd();
    blocks[b].masked = masked.slice(blocks[b].start, end);
  }
  // classify, with namespaces for names and visibility
  const namespaces = [];
  const scopes = []; // {count, visibility}
  const moduleFile = /^module[ \t]*$/m.test(masked);
  for (const blk of blocks) {
    const line = blk.firstLine;
    let m;
    if ((m = NAMESPACE.exec(line))) {
      const parts = m[1].split('.'); namespaces.push(...parts); scopes.push({ count: parts.length, vis: null, expose: false });
      blk.kind = 'context';
    } else if ((m = SECTION.exec(line))) {
      const words = m[1].split(/\s+/).filter(Boolean);
      scopes.push({ count: 0, vis: words.includes('public') ? 'public' : words.includes('private') ? 'private' : null, expose: /@\[expose\]/.test(line) });
      blk.kind = 'context';
    } else if (END.test(line)) {
      const s = scopes.pop(); if (s && s.count) namespaces.splice(namespaces.length - s.count, s.count);
      blk.kind = 'context';
    } else if ((m = DECL.exec(line))) {
      const modifiers = m[1].split(/\s+/).filter(Boolean);
      const declKind = m[2];
      const rawName = m[3];
      blk.kind = 'decl'; blk.declKind = declKind; blk.modifiers = modifiers;
      blk.name = rawName === undefined ? `<anonymous ${declKind} at offset ${blk.start}>` : qualifiedName(namespaces, rawName);
      let def = null;
      for (let k = scopes.length - 1; k >= 0; k--) if (scopes[k].vis) { def = scopes[k].vis; break; }
      if (def === null) def = moduleFile ? 'private' : 'public';
      blk.exported = !modifiers.includes('private') && (modifiers.includes('public') || def === 'public');
      // everything before the declaration keyword: blanks, attributes, `open ... in` and `set_option ... in` prefixes
      blk.attributeText = /^(?:\s+|@\[[^\]]*\]|(?:open|set_option)\b[^\n]*?\bin\b)*/.exec(blk.masked)[0];
      blk.attributes = [...blk.attributeText.matchAll(/@\[([^\]]*)\]/g)].map((x) => x[1].trim());
      blk.exposed = scopes.some((s) => s.expose) || blk.attributes.some((a) => /(?:^|,)\s*expose\s*(?:,|$)/.test(a));
    } else if (OPEN.test(line) || UNIVERSE.test(line)) blk.kind = 'context';
    else blk.kind = 'unsupported';
    // Context commands occupy exactly one code line in the restricted challenge format.
    // Otherwise a semicolon or trailing command could be hidden behind a namespace/end/open command.
    if (blk.kind === 'context' && blk.masked.trim() !== line.trim()) blk.kind = 'unsupported';
  }
  // context signature: the texts of all context blocks before each block
  const sig = [];
  for (const blk of blocks) {
    blk.contextBefore = sig.slice();
    if (blk.kind === 'context') sig.push(blk.text);
  }
  return { imports, badImportLines, blocks, masked, grammarErrors };
}

const SORRY = /\bsorry\w*/;
// a command keyword that starts an indented line (after attributes and modifiers) is a command hidden from the
// column-0 scan, or a command after a one-line docstring; neither appears in an honest challenge or solution
const INDENTED_COMMAND = new RegExp(
  String.raw`^[ \t]+(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|public|meta|noncomputable|local|scoped|unsafe|partial|nonrec)[ \t]+)*` +
  String.raw`(axiom|instance|def|abbrev|structure|class|inductive|opaque|attribute|open|export|namespace|section|end|notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|set_option|universe|variable|initialize|run_cmd|import|theorem|lemma|example)\b`);
const NATIVE = /\bofReduceBool\b|\btrustCompiler\b|\bnative_decide\b|\bdecide[ \t]*\+[ \t]*native\b|\bnative[ \t]*:=[ \t]*true\b/;
const COMMAND_ESCAPE = /#[A-Za-z_]|\b(?:run_cmd|run_elab|run_tac|initialize|builtin_initialize|macro|macro_rules|syntax|elab|implemented_by|extern|unsafe|partial)\b/;
const SORRY_PROOF = /:=[ \t\r\n]*(?:by[ \t\r\n]+)?sorry[ \t\r\n]*$/;

function firstDifference(a, b) {
  const al = a.split('\n'); const bl = b.split('\n');
  for (let k = 0; k < Math.max(al.length, bl.length); k++) {
    if (al[k] !== bl[k]) return `line ${k + 1} of the declaration: challenge ${JSON.stringify(al[k] ?? '(missing)')}, solution ${JSON.stringify(bl[k] ?? '(missing)')}`;
  }
  return 'texts differ';
}

export function checkProject(root, configPath) {
  const errors = []; const warnings = []; const notes = [];
  const rel = path.relative(root, configPath);
  let data;
  try { data = JSON.parse(fs.readFileSync(configPath, 'utf8')); }
  catch (e) { return { errors: [`${rel}: unreadable: ${e.message}`], warnings, notes }; }
  if (data === null || typeof data !== 'object' || Array.isArray(data)) return { errors: [`${rel}: expected a JSON object`], warnings, notes };
  const names = data.theorem_names;
  let theoremNames = [];
  if (!Array.isArray(names) || names.length === 0 || !names.every((x) => typeof x === 'string' && CONFIG_NAME.test(x)) || new Set(names).size !== names.length) errors.push(`${rel}: theorem_names must be a nonempty list of unique qualified names`);
  else theoremNames = names;
  if (!Array.isArray(data.permitted_axioms) || data.permitted_axioms.length !== 3 || new Set(data.permitted_axioms).size !== 3 || !data.permitted_axioms.every((a) => STANDARD_AXIOMS.has(a))) errors.push(`${rel}: permitted_axioms must name exactly propext, Classical.choice, Quot.sound`);
  if (data.enable_nanoda !== true) errors.push(`${rel}: enable_nanoda must be true`);
  const modules = {};
  for (const key of ['challenge_module', 'solution_module']) {
    const mod = data[key];
    if (typeof mod !== 'string' || !CONFIG_NAME.test(mod)) { errors.push(`${rel}: ${key} must be a qualified module name`); continue; }
    const file = path.join(root, mod.replaceAll('.', '/') + '.lean');
    if (!fs.existsSync(file) || !fs.statSync(file).isFile()) { errors.push(`${rel}: ${key} ${mod} has no file ${path.relative(root, file)}`); continue; }
    const text = fs.readFileSync(file, 'utf8');
    modules[key] = { mod, file, text, parsed: parseModule(text) };
  }
  const ch = modules.challenge_module; const so = modules.solution_module;
  if (ch) {
    const lines = ch.text.split('\n').length - (ch.text.endsWith('\n') ? 1 : 0);
    const bytes = Buffer.byteLength(ch.text, 'utf8');
    if (lines > CHALLENGE_MAX_LINES || bytes > CHALLENGE_MAX_BYTES) errors.push(`challenge has ${lines} lines and ${bytes} bytes (limit ${CHALLENGE_MAX_LINES} lines, ${CHALLENGE_MAX_BYTES} bytes)`);
    else if (lines > CHALLENGE_REVIEW_LINES || bytes > CHALLENGE_REVIEW_BYTES) warnings.push(`challenge has ${lines} lines and ${bytes} bytes (review threshold ${CHALLENGE_REVIEW_LINES} lines, ${CHALLENGE_REVIEW_BYTES} bytes)`);
    notes.push(`${lines} lines`);
    for (const imp of ch.parsed.imports) if (imp !== 'Mathlib' && !imp.startsWith('Mathlib.')) errors.push(`challenge imports ${imp}, which is not a Mathlib module`);
    if (ch.parsed.imports.length === 0) warnings.push('challenge has no imports');
  }
  const projectImport = /^(?:Mathlib|LPPDifferentiability(?:Statements|Audit)?|ProbabilityBasics|LPP_Foundations|Martin2004|Differentiability)(?:\.|$)/;
  if (so) for (const imp of so.parsed.imports) if (!projectImport.test(imp)) warnings.push(`solution imports ${imp}, which is neither Mathlib nor a project module; check that it adds no notation or instance (see compare-challenge-types.mjs)`);
  if (so && ch && so.parsed.imports.includes(ch.mod)) errors.push(`solution imports the challenge module ${ch.mod}`);
  for (const [label, m] of [['challenge', ch], ['solution', so]]) {
    if (!m) continue;
    errors.push(...m.parsed.grammarErrors.map((e) => `${label}: ${e}`));
    for (const blk of m.parsed.blocks) {
      if (blk.kind === 'unsupported') errors.push(`${label}: unsupported top-level command ${JSON.stringify(blk.firstLine.slice(0, 100))}`);
      if (blk.kind === 'context' && /@\[/.test(blk.masked) &&
          !/^@\[expose\]\s+(?:public\s+)?section(?:\s+\S+)?\s*$/.test(blk.masked.trim())) {
        errors.push(`${label}: unsupported section attribute`);
      }
      if (blk.kind !== 'decl') continue;
      if (!APPROVED_DECLARATIONS.has(blk.declKind)) errors.push(`${label}: unsupported declaration kind ${blk.declKind}`);
      for (const modifier of blk.modifiers) if (!APPROVED_MODIFIERS.has(modifier)) errors.push(`${label}: unsupported declaration modifier ${modifier}`);
      const allowedAttributes = ['theorem', 'lemma'].includes(blk.declKind) ? ['expose', 'simp'] : ['expose'];
      for (const attribute of blk.attributes) {
        if (!attribute.split(',').every((a) => allowedAttributes.includes(a.trim()))) errors.push(`${label}: unsupported attribute [${attribute}] on ${blk.name}`);
      }
      if (blk.modifiers.includes('private')) errors.push(`${label}: private declaration ${blk.name}`);
      else if (!blk.exported) errors.push(`${label}: declaration ${blk.name} is not exported (no public section or public modifier)`);
      if (blk.declKind === 'axiom') errors.push(`${label}: axiom ${blk.name}`);
    }
    if (/\badmit\b/.test(m.parsed.masked)) errors.push(`${label}: uses admit`);
    if (NATIVE.test(m.parsed.masked)) errors.push(`${label}: uses native evaluation (native_decide, decide +native, ofReduceBool)`);
    if (COMMAND_ESCAPE.test(m.parsed.masked)) errors.push(`${label}: evaluation, syntax, unsafe or implementation-changing command is forbidden`);
    if (/\baxiom\b/.test(m.parsed.masked)) errors.push(`${label}: the word axiom appears in code`);
    if (/\bprivate\b/.test(m.parsed.masked)) errors.push(`${label}: the word private appears in code`);
    if (/\bset_option\b/.test(m.parsed.masked)) errors.push(`${label}: uses set_option`);
    for (const line of m.parsed.masked.split('\n')) {
      const x = INDENTED_COMMAND.exec(line);
      if (x) { errors.push(`${label}: command keyword '${x[1]}' at the start of an indented line: ${JSON.stringify(line.trim().slice(0, 60))}`); break; }
    }
    for (const bad of m.parsed.badImportLines) errors.push(`${label}: import line with more than one import or other text: ${JSON.stringify(bad.slice(0, 80))}`);
    if (!/^\s*module[ \t]*(?:\n|$)/.test(m.parsed.masked)) errors.push(`${label}: the first command is not \`module\``);
    for (const blk of m.parsed.blocks) {
      if (blk.kind === 'decl' && ['def', 'abbrev', 'opaque', 'structure', 'class', 'inductive', 'instance'].includes(blk.declKind) && !blk.exposed) {
        errors.push(`${label}: definition ${blk.name} is not exposed (use \`@[expose] public section\` or \`@[expose]\`)`);
      }
    }
  }
  if (so && SORRY.test(so.parsed.masked)) errors.push('solution contains sorry');
  if (!ch || !so) return { errors, warnings, notes };

  const byName = (parsed) => { const map = new Map(); for (const b of parsed.blocks) if (b.kind === 'decl') { if (map.has(b.name)) errors.push(`duplicate declaration ${b.name}`); map.set(b.name, b); } return map; };
  const chDecls = byName(ch.parsed); const soDecls = byName(so.parsed);
  for (const name of theoremNames) {
    for (const [label, map] of [['challenge', chDecls], ['solution', soDecls]]) {
      const b = map.get(name);
      if (!b || !['theorem', 'lemma'].includes(b.declKind) || !b.exported) errors.push(`${label} does not declare public theorem ${name}`);
    }
    const cb = chDecls.get(name);
    if (cb && !SORRY_PROOF.test(cb.masked)) errors.push(`challenge theorem ${name} does not end with a sorry proof`);
  }
  let compared = 0;
  for (const [name, cb] of chDecls) {
    if (SORRY.test(cb.masked) && !theoremNames.includes(name)) errors.push(`challenge declaration ${name} contains sorry but is not in theorem_names`);
    const sb = soDecls.get(name);
    if (!sb) { errors.push(`solution lacks challenge declaration ${name}`); continue; }
    if (sb.declKind !== cb.declKind) { errors.push(`${name}: challenge ${cb.declKind}, solution ${sb.declKind}`); continue; }
    if (JSON.stringify(cb.contextBefore) !== JSON.stringify(sb.contextBefore)) {
      errors.push(`${name}: the namespace, open, variable or section commands before it differ between challenge and solution`);
      continue;
    }
    if (SORRY.test(cb.masked)) {
      const m = SORRY_PROOF.exec(cb.masked);
      if (!m) { errors.push(`challenge declaration ${name} has a sorry that is not the whole proof`); continue; }
      const statement = cb.text.slice(0, m.index).trimEnd();
      const rest = sb.text.startsWith(statement) ? sb.text.slice(statement.length) : null;
      if (rest === null) errors.push(`${name}: statement differs (${firstDifference(statement, sb.text.slice(0, statement.length + 40))})`);
      else if (!/^[ \t\r\n]*:=/.test(rest)) errors.push(`${name}: the solution statement is longer than the challenge statement`);
      else compared++;
    } else if (cb.text !== sb.text) errors.push(`${name}: differs between challenge and solution (${firstDifference(cb.text, sb.text)})`);
    else compared++;
  }
  for (const [name, sb] of soDecls) {
    if (chDecls.has(name)) continue;
    if (!['theorem', 'lemma'].includes(sb.declKind)) errors.push(`solution adds ${sb.declKind} ${name}; only theorems and lemmas may be added`);
    else if (sb.attributes.some((a) => a !== 'simp')) errors.push(`solution theorem ${name} has attributes [${sb.attributes.join('; ')}]; only simp is allowed`);
  }
  const challengeOrder = [...chDecls.keys()];
  const solutionOrder = [...soDecls.keys()].filter((n) => chDecls.has(n));
  if (JSON.stringify(challengeOrder) !== JSON.stringify(solutionOrder)) errors.push('the challenge declarations occur in a different order in the solution');
  notes.push(`${compared} declarations compared`);
  return { errors, warnings, notes };
}

function main() {
  const args = process.argv.slice(2);
  let root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
  const r = args.indexOf('--root');
  if (r >= 0) root = path.resolve(args[r + 1]);
  const dir = path.join(root, 'comparator');
  const projects = fs.existsSync(dir)
    ? fs.readdirSync(dir).sort().filter((d) => fs.existsSync(path.join(dir, d, 'comparator.json')))
    : [];
  if (projects.length === 0) { console.log('FAIL: no comparator/*/comparator.json found'); return 1; }
  let failed = false;
  for (const p of projects) {
    const { errors, warnings, notes } = checkProject(root, path.join(dir, p, 'comparator.json'));
    if (errors.length) {
      failed = true;
      console.log(`FAIL ${p}`);
      for (const e of errors) console.log(`  - ${e}`);
    } else console.log(`PASS ${p} (${notes.join(', ')})`);
    for (const w of warnings) console.log(`  warning: ${w}`);
  }
  return failed ? 1 : 0;
}

if (process.argv[1] && fs.realpathSync(process.argv[1]) === fs.realpathSync(fileURLToPath(import.meta.url))) process.exitCode = main();
