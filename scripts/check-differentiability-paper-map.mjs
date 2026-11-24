#!/usr/bin/env node
// Check source identity, content locators, map coverage, and Lean export names.
// This reads files only. It does not certify statements, proofs, or axioms.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';

const usage = 'Usage: node scripts/check-differentiability-paper-map.mjs [--root REPOSITORY] [--source LOCAL_TEX]';
const options = {};
for (let i = 2; i < process.argv.length; i += 2) {
  const key = process.argv[i];
  if (!['--root', '--source'].includes(key) || options[key] || !process.argv[i + 1]) throw Error(usage);
  options[key] = process.argv[i + 1];
}
const root = fs.realpathSync(options['--root'] ?? path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..'));
const fail = message => { throw Error(message); };
const sha256 = text => crypto.createHash('sha256').update(text).digest('hex');
const readRoot = relative => fs.readFileSync(repositoryFile(relative), 'utf8');
const mapPath = path.join(root, 'docs/differentiability-paper-map.json');
const map = JSON.parse(fs.readFileSync(mapPath, 'utf8'));
const registry = JSON.parse(fs.readFileSync(path.join(root, 'sources/current-differentiability.json'), 'utf8'));
if (map.version !== 2 || !map.source || !/^[a-f0-9]{64}$/.test(map.source.sha256) ||
    map.source.sha256 !== registry.source.sha256 ||
    map.source.filename !== registry.source.filename || Object.hasOwn(map.source, 'line_count') ||
    registry.guide !== 'docs/guides/differentiability.md' ||
    registry.result_map !== 'docs/differentiability-paper-map.json' ||
    registry.review !== 'docs/reviews/differentiability-final.md' ||
    registry.cited_source_record !== 'sources/current-grs.json' ||
    map.public_guide !== registry.guide || map.source_record !== 'sources/current-differentiability.json' ||
    map.review !== registry.review || Object.hasOwn(map, 'coverage_snapshot') ||
    !Array.isArray(map.results) || !Array.isArray(map.proof_steps) ||
    !Array.isArray(map.active_environments) || !Array.isArray(map.explanatory_scope)) {
  fail('Invalid content-locator map schema or source identity.');
}

function rejectNumericRangeFields(value, trail = 'map') {
  if (!value || typeof value !== 'object') return;
  for (const [key, item] of Object.entries(value)) {
    if (/^(source_lines|proof_lines|line_count)$/.test(key)) fail(`Unstable numeric locator field: ${trail}.${key}`);
    rejectNumericRangeFields(item, `${trail}.${key}`);
  }
}
rejectNumericRangeFields(map);

function repositoryFile(relative) {
  if (typeof relative !== 'string' || path.isAbsolute(relative) || relative.includes('\\') ||
      relative !== path.posix.normalize(relative) || relative.split('/').some(p =>
        ['..', '.', '.git', 'reference', 'references', 'StrictConcavity'].includes(p))) {
    fail(`Invalid differentiability map path: ${relative}`);
  }
  const absolute = fs.realpathSync(path.join(root, relative));
  if (!absolute.startsWith(root + path.sep) || !fs.statSync(absolute).isFile()) {
    fail(`Map path must name a file inside the repository: ${relative}`);
  }
  return absolute;
}

function withoutLeanComments(text) {
  let result = '', depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text.slice(i, i + 2) === '/-') { depth++; i++; continue; }
    if (depth && text.slice(i, i + 2) === '-/') { depth--; i++; continue; }
    if (!depth && text.slice(i, i + 2) === '--') {
      while (i < text.length && text[i] !== '\n') i++;
    }
    result += depth && text[i] !== '\n' ? ' ' : (text[i] ?? '');
  }
  return result;
}

function withoutTexComments(text) {
  return text.split('\n').map(line => {
    for (let i = 0; i < line.length; i++) {
      if (line[i] !== '%') continue;
      let backslashes = 0;
      for (let j = i - 1; j >= 0 && line[j] === '\\'; j--) backslashes++;
      if (backslashes % 2 === 0) return line.slice(0, i);
    }
    return line;
  }).join('\n');
}

let sourceVerified = false, namedResults = null, activeEnvironmentCount = null;
let sourceLines = null, sourceLineHashes = null;
function resolveAnchor(anchor, label) {
  if (!anchor || !/^[a-f0-9]{64}$/.test(anchor.start_sha256) ||
      !/^[a-f0-9]{64}$/.test(anchor.end_sha256) || !/^[a-f0-9]{64}$/.test(anchor.span_sha256)) {
    fail(`Invalid source content locator: ${label}`);
  }
  if (!sourceLines) return null;
  if (!sourceLineHashes) sourceLineHashes = sourceLines.map(sha256);
  const matches = [];
  for (let i = 0; i < sourceLines.length; i++) {
    if (sourceLineHashes[i] !== anchor.start_sha256) continue;
    for (let j = i; j < sourceLines.length; j++) {
      if (sourceLineHashes[j] !== anchor.end_sha256) continue;
      if (sha256(sourceLines.slice(i, j + 1).join('\n')) === anchor.span_sha256) matches.push([i + 1, j + 1]);
    }
  }
  if (matches.length !== 1) fail(`Source locator must resolve uniquely, found ${matches.length}: ${label}`);
  return matches[0];
}

const expectedExportSetHash = '6313d2d09766c189d5a9ddcd442006434b5ad0f55b56d71c10c877d09ffc4adb';
const expectedGuidePaths = ['README.md', 'docs/notation.md', registry.guide,
  registry.review, 'docs/reviews/grs-final-comparison.md'];
const labels = new Set(), statuses = {}, allRows = [...map.results, ...map.proof_steps];
if (map.results.length !== 27 || map.proof_steps.length !== 58 || map.active_environments.length !== 21 ||
    map.explanatory_scope.length !== 9) {
  fail('Map must cover 27 named results, 58 proof entries, 21 active environments, and 9 scope entries.');
}
const expectedStatuses = {
  sealed_main_statement: 1,
  sealed_current_statement: 1,
  reviewed_statement: 16,
  reviewed_composition: 5,
  reviewed_statement_and_proof: 20,
  reviewed_source_composition: 38,
  reviewed_conditional_statement_and_proof: 3,
  source_elementary_implication: 1,
};

for (const row of allRows) {
  if (typeof row.label !== 'string' || !row.label || labels.has(row.label)) fail(`Missing or repeated map label: ${row.label}`);
  labels.add(row.label);
  if (typeof row.status !== 'string' || !row.status || typeof row.proof_route !== 'string' ||
      !row.proof_route || typeof row.notes !== 'string' || !row.notes || !Array.isArray(row.lean)) {
    fail(`Invalid status, proof route, notes, or Lean list: ${row.label}`);
  }
  statuses[row.status] = (statuses[row.status] ?? 0) + 1;
  const publicReview = 'docs/reviews/differentiability-final.md';
  if (JSON.stringify(row.review_evidence) !== JSON.stringify([publicReview])) {
    fail(`Map review evidence must point to the consolidated public review only: ${row.label}`);
  }
  if (/\b(?:lines?|candidate)\s+\d+|\b[0-9a-f]{7,40}\b|docs\/runs|\/Users\/|\/private\/tmp/i.test(row.notes)) {
    fail(`Private provenance or unstable locator in public note: ${row.label}`);
  }
  resolveAnchor(row.source_anchor, row.label);
  for (const [index, anchor] of (row.proof_anchors ?? []).entries()) resolveAnchor(anchor, `${row.label}:proof:${index + 1}`);
}

for (const [index, row] of map.active_environments.entries()) {
  if (!['remark', 'example'].includes(row.kind) || !(row.tex_label === null || typeof row.tex_label === 'string') ||
      !Array.isArray(row.proof_steps) || !row.proof_steps.length) fail(`Invalid active environment entry ${index + 1}.`);
  resolveAnchor(row.source_anchor, `active_environment:${index + 1}`);
}
for (const [index, row] of map.explanatory_scope.entries()) {
  if (!row.status || !row.notes) fail(`Invalid explanatory-scope entry ${index + 1}.`);
  resolveAnchor(row.source_anchor, `explanatory_scope:${index + 1}`);
}
let anchorObjects = 0, anchorDigests = 0;
function countAnchors(value) {
  if (!value || typeof value !== 'object') return;
  if ('start_sha256' in value && 'end_sha256' in value && 'span_sha256' in value) {
    anchorObjects++;
    anchorDigests += Object.keys(value).filter(key => key.endsWith('_sha256')).length;
  }
  for (const child of Object.values(value)) countAnchors(child);
}
countAnchors(map);
if (anchorObjects !== 146 || anchorDigests !== 438) fail(`Source-span anchor inventory differs: ${anchorObjects} spans, ${anchorDigests} digests.`);
if (JSON.stringify(Object.fromEntries(Object.entries(statuses).sort())) !==
    JSON.stringify(Object.fromEntries(Object.entries(expectedStatuses).sort()))) {
  fail('Mapped proof-status counts differ from the reviewed source baseline.');
}

function parseTexEnvironments(text, names) {
  const clean = withoutTexComments(text);
  const begin = new RegExp('\\\\begin\\{(' + names.join('|') + ')\\}(?:\\[[^\\]]*\\])?', 'g');
  const rows = [];
  let match;
  while ((match = begin.exec(clean))) {
    const kind = match[1], closingText = `\\end{${kind}}`;
    const closing = clean.indexOf(closingText, begin.lastIndex);
    if (closing === -1) fail(`Unclosed source environment: ${kind}`);
    const startLine = clean.slice(0, match.index).split('\n').length;
    const endLine = clean.slice(0, closing).split('\n').length;
    const body = clean.slice(match.index, closing);
    const texLabel = body.match(/\\label\{([^}]+)\}/)?.[1] ?? null;
    rows.push({kind, tex_label: texLabel, startLine, endLine, body});
  }
  return rows;
}

if (options['--source']) {
  const raw = fs.readFileSync(options['--source']);
  if (sha256(raw) !== map.source.sha256 || sha256(raw) !== registry.source.sha256) {
    fail('Source SHA-256 differs from the selected draft or source registry.');
  }
  const rawText = raw.toString('utf8');
  sourceLines = rawText.split('\n');
  if (sourceLines.at(-1) === '') sourceLines.pop();
  sourceLineHashes = sourceLines.map(sha256);
  if (sourceLines.length !== registry.source.line_count || rawText.split('\n').length - 1 !== registry.source.newline_count) {
    fail('Source line or newline count differs from the separate source registry.');
  }
  for (const row of allRows) {
    resolveAnchor(row.source_anchor, row.label);
    for (const [index, anchor] of (row.proof_anchors ?? []).entries()) resolveAnchor(anchor, `${row.label}:proof:${index + 1}`);
  }
  for (const [index, row] of map.active_environments.entries()) resolveAnchor(row.source_anchor, `active_environment:${index + 1}`);
  for (const [index, row] of map.explanatory_scope.entries()) resolveAnchor(row.source_anchor, `explanatory_scope:${index + 1}`);

  const resultEnvironments = parseTexEnvironments(rawText, ['theorem', 'lemma', 'proposition', 'corollary', 'definition']);
  const inventory = [];
  for (const env of resultEnvironments) {
    if (!env.tex_label) fail(`Unlabelled named result near source offset ${env.startLine}.`);
    const row = map.results.find(item => item.label === env.tex_label);
    if (!row || row.kind !== env.kind) fail(`Missing or different named result kind: ${env.tex_label}`);
    if (JSON.stringify(resolveAnchor(row.source_anchor, row.label)) !== JSON.stringify([env.startLine, env.endLine])) {
      fail(`Named result content locator does not cover its exact environment: ${row.label}`);
    }
    inventory.push(env.tex_label);
  }
  if (inventory.length !== 27 || new Set(inventory).size !== inventory.length ||
      map.results.some(row => !inventory.includes(row.label))) {
    fail(`Named-result source inventory is incomplete or duplicated: ${inventory.length} source labels, ${new Set(inventory).size} unique.`);
  }

  const texActive = parseTexEnvironments(rawText, ['remark', 'example']);
  const mappedActive = map.active_environments.map((row, index) => {
    const [startLine, endLine] = resolveAnchor(row.source_anchor, `active_environment:${index + 1}`);
    return {...row, startLine, endLine};
  });
  const unmatched = [...texActive];
  for (const row of mappedActive) {
    const index = unmatched.findIndex(env => env.kind === row.kind && env.tex_label === row.tex_label &&
      env.startLine === row.startLine && env.endLine === row.endLine);
    if (index < 0) fail(`Active remark/example locator is absent or mismatched: ${row.tex_label ?? row.kind}`);
    unmatched.splice(index, 1);
  }
  if (unmatched.length || texActive.length !== 21) fail(`Active remark/example inventory mismatch: ${unmatched.length} unmatched.`);

  const proof = new Map(map.proof_steps.map(row => [row.label, row]));
  if (proof.size !== 58) fail('Proof-step labels are not unique.');
  for (const env of mappedActive) {
    for (const label of env.proof_steps) {
      const row = proof.get(label);
      if (!row || JSON.stringify(resolveAnchor(row.source_anchor, label)) !== JSON.stringify([env.startLine, env.endLine])) {
        fail(`Active environment proof entry is absent or has a different source locator: ${label}`);
      }
    }
  }
  sourceVerified = true;
  namedResults = inventory.length;
  activeEnvironmentCount = texActive.length;
}

const leanFiles = new Map(), leanNames = new Set(), reviewPaths = new Set();
for (const row of allRows) {
  for (const target of row.lean) {
    if (typeof target.export !== 'string' || !target.export.includes('.')) fail(`Missing qualified Lean export: ${row.label}`);
    const filename = repositoryFile(target.path);
    if (!leanFiles.has(filename)) leanFiles.set(filename, withoutLeanComments(fs.readFileSync(filename, 'utf8')));
    const shortName = target.export.split('.').at(-1).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const declaration = new RegExp(`\\b(?:theorem|lemma|def|abbrev|structure|inductive|alias|instance)\\s+(?:[A-Za-z0-9_'.]+\\.)?${shortName}(?![A-Za-z0-9_'])`, 'u');
    if (!declaration.test(leanFiles.get(filename))) fail(`Export not declared in mapped file: ${row.label}: ${target.path}: ${target.export}`);
  }
  for (const review of row.review_evidence ?? []) {
    repositoryFile(review);
    reviewPaths.add(review);
  }
}
if (leanNames.size) fail('Internal export inventory error.');
const exportRows = allRows.flatMap(row => row.lean.map(target => ({...target, label: row.label})));
const exportNames = new Set(exportRows.map(target => `${target.path}::${target.export}`));
const exportHash = sha256([...exportNames].sort().join('\n') + '\n');
if (exportNames.size !== 185 || exportHash !== expectedExportSetHash || leanFiles.size !== 122 ||
    reviewPaths.size !== 1 || !reviewPaths.has(registry.review)) {
  fail(`Lean/review inventory differs: ${exportNames.size} exports, ${leanFiles.size} Lean files, ${reviewPaths.size} review paths.`);
}

const guideText = readRoot(registry.guide);
for (const [name, relative] of Object.entries({guide: registry.guide, map: registry.result_map,
  review: registry.review, citedSource: registry.cited_source_record})) repositoryFile(relative);
repositoryFile('sources/current-differentiability.json');
for (const text of [guideText, readRoot(registry.review)]) {
  if (/\blines?\s+\d+\s*[–—-]\s*\d+|\(\s*\d{3,4}\s*[–—-]\s*\d{3,4}\s*\)/i.test(text)) {
    fail('Public guide/review contains a manuscript line-range locator.');
  }
}
for (const row of map.results) {
  if (!guideText.includes(`\`${row.label}\``)) fail(`Current guide omits named result label: ${row.label}`);
}
for (const relative of expectedGuidePaths) {
  const text = readRoot(relative);
  for (const match of text.matchAll(/\]\(([^)\s]+)\)/g)) {
    if (/^(https?:|#)/.test(match[1])) continue;
    const target = path.resolve(path.dirname(repositoryFile(relative)), match[1].split('#')[0]);
    if (!target.startsWith(root + path.sep) || !fs.statSync(target).isFile()) fail(`Invalid guide link: ${relative}: ${match[1]}`);
  }
}

console.log(JSON.stringify({
  verdict: 'metadata_checked', source_sha256: map.source.sha256, source_verified: sourceVerified,
  named_results: namedResults, proof_entries: map.proof_steps.length,
  active_remarks_and_examples: activeEnvironmentCount,
  source_span_anchors: anchorObjects, source_span_digests: anchorDigests,
  mapped_lean_files: leanFiles.size, mapped_qualified_lean_names: exportNames.size,
  export_set_sha256: exportHash, review_paths: reviewPaths.size, guide_links_checked: expectedGuidePaths.length, statuses,
  limits: 'Checks source identity, exact content locators, inventories, links, and declaration names. Mathematical statement and proof fidelity require independent review; Lean validity and axioms require compiler checks.'
}, null, 2));
