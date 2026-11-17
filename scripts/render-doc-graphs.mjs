import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { githubMath } from './github-math.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../docs');
const slugs = ['strong-existence', 'differentiability', 'martin-2004', 'bk-1985', 'liggett-1985'];
const symbols = { certified: '✓', restricted: '◐', not_assessed: '?', not_in_release: '○' };
const names = { certified: 'Certified', restricted: 'Restricted', not_assessed: 'Not assessed', not_in_release: 'Not in this release' };
const clean = value => String(value || '').replaceAll('|', '\\|').replaceAll('\n', ' ');
const quote = value => String(value).replaceAll('&', '&amp;').replaceAll('"', '&quot;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
const key = '**✓ Certified** · **◐ Restricted** · **○ Not in this release** · **? Not assessed**';

function validate(p) {
  const ids = new Set(p.results.map(r => r.id));
  if (ids.size !== p.results.length) throw new Error(`${p.slug}: duplicate result`);
  const owners = new Map();
  for (const c of p.clusters) for (const id of c.members) {
    if (!ids.has(id) || owners.has(id)) throw new Error(`${p.slug}: invalid cluster member ${id}`);
    owners.set(id, c.id);
  }
  for (const r of p.results) {
    if (owners.get(r.id) !== r.cluster) throw new Error(`${p.slug}: missing cluster for ${r.id}`);
    if (!symbols[r.coverage.status]) throw new Error(`${p.slug}: invalid coverage for ${r.id}`);
    if (!r.source || (!r.source.lines && !r.source.locator)) throw new Error(`${p.slug}: no source locator for ${r.id}`);
    if (r.coverage.status === 'certified' && !r.coverage.links.length) throw new Error(`${p.slug}: certified without link ${r.id}`);
    if (r.coverage.status === 'restricted') {
      for (const field of ['label', 'paper_scope', 'certified_scope', 'gap', 'reason', 'impact']) {
        const value = r.coverage.restriction?.[field];
        if (typeof value !== 'string' || !value.trim()) throw new Error(`${p.slug}: restricted without ${field} ${r.id}`);
      }
    }
  }
  const externals = new Set(p.external_inputs.map(e => e.id));
  for (const e of p.edges) {
    if ((!ids.has(e.from) && !externals.has(e.from)) || !ids.has(e.to) || !e.evidence || !e.reason) throw new Error(`${p.slug}: invalid edge ${e.from} -> ${e.to}`);
  }
  return owners;
}

function fullGraph(p) {
  const ids = new Map(p.results.map((r, i) => [r.id, `R${i}`]));
  const resultById = new Map(p.results.map(r => [r.id, r]));
  const lines = ['flowchart TD'];
  for (const [i, c] of p.clusters.entries()) {
    lines.push(`  subgraph S${i}["${quote(c.title)}"]`);
    for (const id of c.members) {
      const r = resultById.get(id);
      lines.push(`    ${ids.get(id)}["${symbols[r.coverage.status]} ${quote(r.label)}<br/>${quote(r.title)}"]`);
    }
    lines.push('  end');
  }
  const seen = new Set();
  for (const e of p.edges) if (ids.has(e.from) && ids.has(e.to)) {
    const pair = `${e.from}\0${e.to}`;
    if (!seen.has(pair)) {
      const suffix = e.route?.includes('bounded') ? '|bounded case|' : e.route?.includes('general') ? '|general weights|' : '';
      lines.push(`  ${ids.get(e.from)} -->${suffix} ${ids.get(e.to)}`);
      seen.add(pair);
    }
  }
  lines.push('  classDef certified fill:#eaf6ec,stroke:#2d8544,color:#163b20', '  classDef restricted fill:#fff5db,stroke:#a77815,color:#594005', '  classDef not_assessed fill:#f6f8fa,stroke:#8c959f,stroke-dasharray:4 3,color:#424a53', '  classDef not_in_release fill:#fff,stroke:#8c959f,color:#59636e');
  for (const r of p.results) lines.push(`  class ${ids.get(r.id)} ${r.coverage.status}`);
  return lines.join('\n');
}

function overview(p) {
  const ids = new Map(p.clusters.map((c, i) => [c.id, `C${i}`]));
  const lines = ['flowchart TD'];
  for (const c of p.clusters) {
    const labels = c.members.map(id => p.results.find(r => r.id === id).label.replace('Theorem ', 'Thm. ').replace('Lemma ', 'Lem. ').replace('Proposition ', 'Prop. ').replace('Corollary ', 'Cor. '));
    const parts = [];
    for (let i = 0; i < labels.length; i += 3) parts.push(labels.slice(i, i + 3).join(' · '));
    lines.push(`  ${ids.get(c.id)}["${quote(c.title)}<br/>${parts.map(quote).join('<br/>')}"]`);
  }
  for (const e of p.overview_edges) {
    const from = e.from || e[0], to = e.to || e[1];
    if (!ids.has(from) || !ids.has(to)) throw new Error(`${p.slug}: missing overview group`);
    lines.push(`  ${ids.get(from)} --> ${ids.get(to)}`);
  }
  return lines.join('\n');
}

const resultAnchor = r => r.label.toLowerCase().replace(/[^\w\- ]/g, '').replace(/ /g, '-');

function progress(p, mapPath = '') {
  const out = ['| Paper result | Formalization |', '| --- | --- |'];
  for (const c of p.clusters) for (const id of c.members) {
    const r = p.results.find(x => x.id === id), cov = r.coverage;
    const links = cov.links.map(l => `[${clean(l.label || 'Lean certificate')}](${l.url})`).join(' · ');
    const scopeLabel = cov.status === 'restricted' ? cov.restriction.label : 'Coverage note';
    const scopeLink = `[${clean(scopeLabel)}](${mapPath}#${resultAnchor(r)})`;
    out.push(`| **[${clean(r.label)}](${mapPath}#${resultAnchor(r)})**<br/>${clean(r.title)} | **${symbols[cov.status]} ${names[cov.status]}**<br/>${scopeLink}${links ? '<br/>' + links : ''} |`);
  }
  return out.join('\n');
}

function coverageNotes(p) {
  return p.clusters.flatMap(c => c.members).map(id => {
    const r = p.results.find(item => item.id === id), cov = r.coverage;
    const loc = r.source.page ? 'p. ' + r.source.page : r.source.lines ? 'lines ' + r.source.lines.join('–') : r.source.locator;
    const definitions = (r.definitions || []).map(d => typeof d === 'string' ? d : d.text || d.definition || '').filter(Boolean).join('\n\n');
    const links = cov.links.map(l => `[${l.label || 'Lean certificate'}](${l.url})`).join(' · ');
    const scope = cov.status === 'restricted' ? [
      `**${cov.restriction.label}**`,
      '**Paper scope**\n\n' + cov.restriction.paper_scope,
      '**Certified scope**\n\n' + cov.restriction.certified_scope,
      '**Remaining gap**\n\n' + cov.restriction.gap,
      '**Why this scope**\n\n' + cov.restriction.reason,
      '**Effect on main results**\n\n' + cov.restriction.impact
    ].join('\n\n') : cov.scope;
    return `### ${r.label}\n\n**${r.title}**\n\n${r.summary}\n\n${definitions ? definitions + '\n\n' : ''}**${symbols[cov.status]} ${names[cov.status]}**\n\n${scope}\n\n${links ? links + '\n\n' : ''}*Source location* ${loc}.\n`;
  }).join('\n');
}

const reports = [];
for (const slug of slugs) {
  const dataPath = path.join(root, 'graphs/paper-results', slug + '.json');
  const p = JSON.parse(await fs.readFile(dataPath, 'utf8'));
  validate(p);
  const graph = fullGraph(p), table = progress(p);
  const guideTable = progress(p, `../graphs/paper-results/${slug}.md`);
  const main = `## Progress and dependencies\n\n[Dependency graph and coverage notes](../graphs/paper-results/${p.slug}.md)\n\nThe graph and progress list cover every named result. Follow a result link to read its coverage and open its certificates.\n\n<details>\n<summary>Dependency overview</summary>\n\n\`\`\`mermaid\n${overview(p)}\n\`\`\`\n\n</details>\n\n${p.notes.map(n => n + '\n\n').join('')}<details>\n<summary>Every result and its status</summary>\n\n${key}\n\n\`\`\`mermaid\n${graph}\n\`\`\`\n\n${guideTable}\n\n</details>\n\n`;
  const guidePath = path.join(root, 'guides', slug + '.md');
  let guide = await fs.readFile(guidePath, 'utf8');
  if (guide.includes('<!-- PAPER_MAP -->')) guide = guide.replace('<!-- PAPER_MAP -->', '<!-- PAPER_MAP_START -->\n' + main + '<!-- PAPER_MAP_END -->');
  else if (guide.includes('<!-- PAPER_MAP_START -->')) guide = guide.replace(/<!-- PAPER_MAP_START -->[\s\S]*?<!-- PAPER_MAP_END -->/, '<!-- PAPER_MAP_START -->\n' + main + '<!-- PAPER_MAP_END -->');
  else throw new Error(`${slug}: no graph insertion marker`);
  await fs.writeFile(guidePath, githubMath(guide));
  const uses = p.edges.map(e => {
    const from = p.results.find(r => r.id === e.from) || p.external_inputs.find(r => r.id === e.from);
    const to = p.results.find(r => r.id === e.to);
    return `| ${clean(from.label || from.title)} → ${clean(to.label)} | ${clean(typeof e.evidence === 'string' ? e.evidence : [e.evidence.page ? 'p. ' + e.evidence.page : '', e.evidence.locator].filter(Boolean).join(' · '))} |`;
  }).join('\n');
  const out = `# ${p.title}\n\n**${p.authors.join(', ')}**\n\n[Formalization guide](../../guides/${slug}.md) · [Paper catalogue](../../../README.md)\n\n${key}\n\nA status applies to the scope stated below. Arrows point from a result to a result whose proof uses it.\n\n\`\`\`mermaid\n${graph}\n\`\`\`\n\n${p.notes.map(n => n + '\n\n').join('')}## Progress\n\n${table}\n\n## Coverage notes\n\nThese short descriptions locate the results and explain certificate coverage. Consult the paper for the full statements and proofs; the formalization guide states the main certified theorems.\n\n${coverageNotes(p)}\n\n<details>\n<summary>Source locations for dependency arrows</summary>\n\n| Use | Source location |\n| --- | --- |\n${uses}\n\n</details>\n`;
  await fs.writeFile(path.join(root, 'graphs/paper-results', slug + '.md'), githubMath(out));
  reports.push({ paper: p.title, results: p.results.length, source_edges: p.edges.length, clusters: p.clusters.length });
}
console.log(JSON.stringify(reports, null, 2));
