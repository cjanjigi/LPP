/* The graph and the accessible result list are two views of the same paper data. */
'use strict';

const ui = Object.fromEntries([
  'paper-select', 'paper-title', 'paper-authors', 'guide-link', 'result-search',
  'search-results', 'expand-all', 'collapse-all', 'fit-map', 'show-external',
  'graph', 'graph-error', 'graph-summary', 'zoom-in', 'zoom-out', 'focus-result',
  'result-detail', 'all-results', 'all-results-title', 'result-list'
].map(id => [id, document.getElementById(id)]));

const statuses = {
  certified: { symbol: '✓', label: 'Certified', className: 'certified' },
  restricted: { symbol: '◐', label: 'Restricted', className: 'restricted' },
  not_assessed: { symbol: '?', label: 'Not assessed', className: 'not-assessed' },
  not_in_release: { symbol: '○', label: 'Not in this release', className: 'not-in-release' }
};

let paper;
let results = new Map();
let externals = new Map();
let groups = [];
let groupFor = new Map();
let expanded = new Set();
let selected = null;
let cy = null;
let loadNumber = 0;
let visibleIds = new Map();

function element(tag, className, text) {
  const el = document.createElement(tag);
  if (className) el.className = className;
  if (text !== undefined && text !== null) el.textContent = String(text);
  return el;
}

function statusFor(result) {
  return statuses[result.coverage?.status] || statuses.not_assessed;
}

function statusBadge(result) {
  const s = statusFor(result);
  return element('span', `status ${s.className}`, `${s.symbol} ${s.label}`);
}

function labelFor(result) {
  return result.label || result.number || result.id;
}

function addLink(parent, label, href, className) {
  if (!href) return;
  let url;
  try { url = new URL(href, location.href); } catch { return; }
  if (!['http:', 'https:'].includes(url.protocol)) return;
  const link = element('a', className, label);
  link.href = url.href;
  if (url.origin !== location.origin) {
    link.target = '_blank';
    link.rel = 'noopener noreferrer';
  }
  parent.append(link);
}

function linesText(lines) {
  if (!Array.isArray(lines)) return lines ? String(lines) : '';
  if (lines.some(Array.isArray)) return lines.map(linesText).join(', ');
  return lines.length === 2 ? `${lines[0]}–${lines[1]}` : lines.join(', ');
}

function sourceText(source) {
  if (!source) return '';
  if (Array.isArray(source)) return `lines ${linesText(source)}`;
  if (typeof source === 'string') {
    // Do not put a workstation file path in the reader interface.
    const match = source.match(/(?:@?L)(\d+)(?:[-–]L?(\d+))?/);
    if (match) return `lines ${match[1]}${match[2] ? `–${match[2]}` : ''}`;
    return source.startsWith('/') ? '' : source;
  }
  const parts = [];
  if (source.page || source.pages) parts.push(`page ${source.page || source.pages}`);
  if (source.lines || source.statement_lines) parts.push(`lines ${linesText(source.lines || source.statement_lines)}`);
  if (source.locator) parts.push(String(source.locator));
  return parts.join(' · ');
}

function updateLocation(resultId) {
  const url = new URL(location.href);
  url.searchParams.set('paper', paper.slug);
  if (resultId) url.searchParams.set('result', resultId);
  else url.searchParams.delete('result');
  history.replaceState(null, '', url);
}

function nodeHeight(result) {
  return Math.max(82, 34 + Math.ceil(String(result.title || '').length / 25) * 18);
}

function groupCounts(group) {
  const counts = {};
  for (const id of group.members) {
    const key = results.get(id)?.coverage?.status || 'not_assessed';
    counts[key] = (counts[key] || 0) + 1;
  }
  return Object.entries(counts).map(([key, count]) => `${statuses[key]?.symbol || '?'} ${count}`).join('   ');
}

/* Collapsing a section projects its edges onto one box. SCCs keep the layout
   usable when two sections genuinely use different results from one another. */
function groupRanks(ids, arrows) {
  const adjacency = new Map(ids.map(id => [id, new Set()]));
  for (const [from, to] of arrows) if (from !== to && adjacency.has(from) && adjacency.has(to)) adjacency.get(from).add(to);
  let next = 0;
  const index = new Map(), low = new Map(), stack = [], onStack = new Set(), components = [];
  function visit(id) {
    index.set(id, next); low.set(id, next++); stack.push(id); onStack.add(id);
    for (const target of adjacency.get(id)) {
      if (!index.has(target)) { visit(target); low.set(id, Math.min(low.get(id), low.get(target))); }
      else if (onStack.has(target)) low.set(id, Math.min(low.get(id), index.get(target)));
    }
    if (low.get(id) === index.get(id)) {
      const component = [];
      let item;
      do { item = stack.pop(); onStack.delete(item); component.push(item); } while (item !== id);
      components.push(component);
    }
  }
  ids.forEach(id => { if (!index.has(id)) visit(id); });
  const owner = new Map(); components.forEach((items, i) => items.forEach(id => owner.set(id, i)));
  const parents = components.map(() => new Set());
  for (const [from, tos] of adjacency) for (const to of tos) if (owner.get(from) !== owner.get(to)) parents[owner.get(to)].add(owner.get(from));
  const ranks = new Map();
  function rank(i) {
    if (!ranks.has(i)) ranks.set(i, parents[i].size ? 1 + Math.max(...Array.from(parents[i], rank)) : 0);
    return ranks.get(i);
  }
  return new Map(ids.map(id => [id, rank(owner.get(id))]));
}

function graphElements() {
  const elements = [];
  const layouts = [];
  visibleIds = new Map();
  for (const group of groups) {
    const members = group.members.map(id => results.get(id)).filter(Boolean);
    if (!members.length) continue;
    const isOpen = expanded.has(group.id) || members.length === 1;
    const layout = { id: group.id, members, open: isOpen, external: false };
    if (members.length === 1) {
      layout.width = 218; layout.height = nodeHeight(members[0]);
    } else if (isOpen) {
      layout.columns = members.length > 3 ? 2 : 1;
      layout.rows = Math.ceil(members.length / layout.columns);
      layout.rowHeight = Math.max(...members.map(nodeHeight)) + 35;
      layout.width = layout.columns * 218 + 46;
      layout.height = layout.rows * layout.rowHeight + 50;
      elements.push({ data: { id: `g::${group.id}`, label: `${group.title}  −`, type: 'section', height: 100 }, classes: 'section' });
    } else {
      layout.width = 268; layout.height = 112;
      elements.push({ data: { id: `g::${group.id}`, label: `${group.title}\n${members.length} results\n${groupCounts(group)}\nClick to expand`, type: 'group', groupId: group.id, height: 108 }, classes: 'group' });
    }
    for (const result of members) {
      const id = isOpen ? `r::${result.id}` : `g::${group.id}`;
      visibleIds.set(result.id, id);
      if (!isOpen) continue;
      const s = statusFor(result);
      const data = { id, resultId: result.id, type: 'result', label: `${s.symbol} ${labelFor(result)}\n${result.title}`, height: nodeHeight(result) };
      if (members.length > 1) data.parent = `g::${group.id}`;
      const kind = String(result.kind || '').toLowerCase();
      elements.push({ data, classes: `result ${s.className} ${kind === 'theorem' ? 'theorem' : ''}` });
    }
    layouts.push(layout);
  }
  if (ui['show-external'].checked) {
    for (const input of externals.values()) {
      const id = `x::${input.id}`;
      layouts.push({ id, width: 218, height: Math.max(80, 30 + Math.ceil(input.title.length / 26) * 17), external: true, input });
      elements.push({ data: { id, type: 'external', externalId: input.id, label: input.title, height: layouts.at(-1).height }, classes: 'external' });
      visibleIds.set(input.id, id);
    }
  }
  const projected = new Map();
  for (const edge of paper.edges || []) {
    const from = visibleIds.get(edge.from), to = visibleIds.get(edge.to);
    if (!from || !to || from === to) continue;
    const key = `${from}\u0000${to}`;
    if (!projected.has(key)) projected.set(key, { from, to, sourceEdges: [] });
    projected.get(key).sourceEdges.push(edge);
  }
  let edgeIndex = 0;
  for (const edge of projected.values()) elements.push({ data: { id: `edge-${edgeIndex++}`, source: edge.from, target: edge.to, sourceEdges: edge.sourceEdges }, classes: edge.sourceEdges.every(e => e.route === 'bounded-proof') ? 'bounded-route' : '' });

  const owner = id => results.has(id) ? groupFor.get(id) : `x::${id}`;
  const arrows = (paper.edges || []).map(e => [owner(e.from), owner(e.to)]);
  const ranks = groupRanks(layouts.map(g => g.id), arrows);
  const rows = new Map();
  for (const group of layouts) {
    const rank = ranks.get(group.id) || 0;
    if (!rows.has(rank)) rows.set(rank, []);
    rows.get(rank).push(group);
  }
  const positions = new Map();
  let top = 40;
  for (const [, row] of Array.from(rows).sort((a, b) => a[0] - b[0])) {
    const rowHeight = Math.max(...row.map(g => g.height));
    const totalWidth = row.reduce((sum, g) => sum + g.width, 0) + (row.length - 1) * 70;
    let left = -totalWidth / 2;
    for (const group of row) {
      const cx = left + group.width / 2;
      const cy = top + rowHeight / 2;
      if (group.external) positions.set(group.id, { x: cx, y: cy });
      else if (!group.open) positions.set(`g::${group.id}`, { x: cx, y: cy });
      else if (group.members.length === 1) positions.set(`r::${group.members[0].id}`, { x: cx, y: cy });
      else {
        group.members.forEach((result, i) => {
          const column = i % group.columns, rowIndex = Math.floor(i / group.columns);
          positions.set(`r::${result.id}`, {
            x: cx + (column - (group.columns - 1) / 2) * 218,
            y: cy - (group.rows - 1) * group.rowHeight / 2 + rowIndex * group.rowHeight + 12
          });
        });
      }
      left += group.width + 70;
    }
    top += rowHeight + 115;
  }
  for (const node of elements) if (!node.data.source && positions.has(node.data.id)) node.position = positions.get(node.data.id);
  return elements;
}

const graphStyle = [
  { selector: 'node', style: { 'shape': 'roundrectangle', 'label': 'data(label)', 'text-wrap': 'wrap', 'text-max-width': 184, 'font-family': '-apple-system, BlinkMacSystemFont, Segoe UI, sans-serif', 'font-size': 12, 'line-height': 1.35, 'color': '#26362e', 'text-valign': 'center', 'text-halign': 'center', 'background-color': '#fff', 'border-color': '#aebcb5', 'border-width': 1.4, 'width': 198, 'height': 'data(height)', 'padding': 5, 'overlay-opacity': 0 } },
  { selector: 'node.theorem', style: { 'background-color': '#fff1da', 'font-weight': 650 } },
  { selector: 'node.certified', style: { 'border-color': '#287255', 'border-width': 2.6 } },
  { selector: 'node.restricted', style: { 'border-color': '#b48336', 'border-width': 2.4, 'border-style': 'dashed' } },
  { selector: 'node.not-in-release', style: { 'background-color': '#f4f4f2', 'border-color': '#87908f', 'border-style': 'dotted' } },
  { selector: 'node.group', style: { 'width': 258, 'height': 108, 'background-color': '#eff4f0', 'border-color': '#829e90', 'border-width': 1.8, 'font-size': 13, 'text-max-width': 240, 'font-weight': 600 } },
  { selector: 'node.section', style: { 'background-color': '#f6f9f6', 'background-opacity': .65, 'border-color': '#a7b9ad', 'border-width': 1.2, 'border-style': 'dashed', 'padding': 24, 'text-valign': 'top', 'text-margin-y': -9, 'font-size': 13, 'font-weight': 650, 'text-max-width': 420, 'compound-sizing-wrt-labels': 'include' } },
  { selector: 'node.external', style: { 'background-color': '#f4f3f0', 'border-color': '#a29f93', 'border-style': 'dashed', 'font-size': 11 } },
  { selector: 'edge', style: { 'width': 1.5, 'line-color': '#afbeb5', 'target-arrow-color': '#91a69a', 'target-arrow-shape': 'triangle', 'arrow-scale': .8, 'curve-style': 'bezier', 'opacity': .8, 'overlay-opacity': 0 } },
  { selector: 'edge.bounded-route', style: { 'line-style': 'dashed' } },
  { selector: '.muted', style: { 'opacity': .24 } },
  { selector: 'edge.highlight', style: { 'line-color': '#c57b2c', 'target-arrow-color': '#c57b2c', 'width': 2.8, 'opacity': 1, 'z-index': 5 } },
  { selector: 'node.highlight', style: { 'opacity': 1, 'border-width': 3 } },
  { selector: 'node.selected-result', style: { 'border-color': '#b5681c', 'border-width': 4, 'background-color': '#fff2db', 'opacity': 1, 'z-index': 10 } }
];

function graphHighlight(id = selected) {
  if (!cy) return;
  cy.elements().removeClass('highlight muted selected-result');
  if (!id || !visibleIds.has(id)) return;
  const node = cy.getElementById(visibleIds.get(id));
  if (!node.length) return;
  const neighbors = node.closedNeighborhood();
  cy.elements().difference(neighbors.union(node.parents())).addClass('muted');
  neighbors.addClass('highlight');
  node.addClass('selected-result');
}

function drawGraph({ fit = true } = {}) {
  if (!paper) return;
  const elements = graphElements();
  if (!window.cytoscape) {
    ui['graph-error'].hidden = false;
    ui['graph-error'].textContent = 'The graph library could not load. Use search or the complete result list to inspect every result and its dependencies.';
    ui['all-results'].open = true;
    ui['graph-summary'].textContent = `${paper.results.length} results available in the list.`;
    document.documentElement.dataset.paperMapReady = 'fallback';
    return;
  }
  if (!cy) {
    cy = cytoscape({ container: ui.graph, elements: [], style: graphStyle, minZoom: .12, maxZoom: 2.8, wheelSensitivity: .2, layout: { name: 'preset' }, boxSelectionEnabled: false });
    cy.on('tap', 'node', event => {
      const node = event.target;
      if (node.data('type') === 'group') toggleGroup(node.data('groupId'));
      else if (node.data('type') === 'section') toggleGroup(node.id().slice(3));
      else if (node.data('type') === 'result') selectResult(node.data('resultId'), { openGroup: false });
      else if (node.data('type') === 'external') showExternal(node.data('externalId'));
    });
    cy.on('tap', 'edge', event => showEdge(event.target.data('sourceEdges')));
    cy.on('mouseover', 'node', event => {
      ui.graph.style.cursor = 'pointer';
      const node = event.target;
      if (node.data('type') === 'result') graphHighlight(node.data('resultId'));
    });
    cy.on('mouseout', 'node', () => { ui.graph.style.cursor = 'grab'; graphHighlight(); });
    cy.on('tap', event => { if (event.target === cy) graphHighlight(); });
    new ResizeObserver(() => cy?.resize()).observe(ui.graph);
  }
  cy.batch(() => { cy.elements().remove(); cy.add(elements); });
  cy.layout({ name: 'preset', fit: false }).run();
  cy.resize();
  if (fit) {
    cy.fit(undefined, 32);
    if (cy.zoom() < .7) {
      const bounds = cy.elements().boundingBox();
      cy.zoom(.7);
      cy.pan({ x: 24 - bounds.x1 * .7, y: 24 - bounds.y1 * .7 });
    }
  }
  graphHighlight();
  const visible = cy.nodes('.result').length;
  ui.graph.dataset.visibleResults = String(visible);
  ui.graph.dataset.totalResults = String(paper.results.length);
  ui['graph-summary'].textContent = visible === paper.results.length
    ? `All ${paper.results.length} results expanded.`
    : `${paper.results.length} results in the map · ${visible} shown individually.`;
  document.documentElement.dataset.paperMapReady = 'true';
  updateGroupButtons();
}

function toggleGroup(id) {
  if (expanded.has(id)) expanded.delete(id); else expanded.add(id);
  drawGraph();
}

function updateGroupButtons() {
  for (const button of ui['result-list'].querySelectorAll('[data-group]')) {
    const open = expanded.has(button.dataset.group);
    button.setAttribute('aria-expanded', String(open));
    button.textContent = `${open ? '−' : '+'} ${button.dataset.title}`;
  }
}

function renderAllResults() {
  ui['result-list'].replaceChildren();
  ui['all-results-title'].textContent = `All results (${paper.results.length})`;
  for (const group of groups) {
    const section = element('div', 'result-group');
    if (group.members.length > 1) {
      const button = element('button', 'group-toggle');
      button.type = 'button'; button.dataset.group = group.id; button.dataset.title = group.title;
      button.addEventListener('click', () => toggleGroup(group.id)); section.append(button);
    } else section.append(element('h3', '', group.title));
    for (const id of group.members) {
      const result = results.get(id);
      if (!result) continue;
      const button = element('button', 'result-choice');
      button.type = 'button'; button.dataset.result = id;
      button.append(element('span', 'choice-label', labelFor(result)), element('span', 'choice-name', result.title), statusBadge(result));
      button.addEventListener('click', () => selectResult(id));
      section.append(button);
    }
    ui['result-list'].append(section);
  }
  updateGroupButtons();
}

function showIntroduction() {
  const detail = ui['result-detail']; detail.replaceChildren();
  detail.append(element('p', 'intro-kicker', 'Explore the paper'), element('h2', '', 'Results and their dependencies'));
  detail.append(element('p', '', 'Open a group to see its individual results. Select a result to read its summary, trace the results it uses, and inspect its formalization status.'));
  const list = element('ul', 'intro-list');
  for (const text of ['Expand all reveals every result in the paper map.', 'A green check links to a released certificate. A restricted result explains exactly which part is covered.', 'Search and the complete result list provide the same navigation as the graph.']) list.append(element('li', '', text));
  detail.append(list);
  const guide = element('p'); addLink(guide, 'Read the precise certified statements in the formalization guide', paper.guide); detail.append(guide);
  if (paper.notes?.length) {
    const notes = element('details', 'source-notes'); notes.append(element('summary', '', 'Scope of this map'));
    for (const note of paper.notes) notes.append(element('p', '', typeof note === 'string' ? note : note.text || note.note || JSON.stringify(note)));
    detail.append(notes);
  }
}

function evidenceText(edge) {
  if (typeof edge.evidence === 'string') return sourceText(edge.evidence);
  return sourceText(edge.evidence || edge.source || edge.consumer_use);
}

function revealDetail() {
  const panel = document.getElementById('reading-panel');
  panel.scrollTop = 0;
  if (matchMedia('(max-width: 900px)').matches) ui['result-detail'].scrollIntoView({ block: 'start' });
}

let mathQueue = Promise.resolve();
function typesetDetail() {
  document.documentElement.dataset.resultMathReady = 'false';
  mathQueue = mathQueue.catch(() => {}).then(async () => {
    if (window.MathJax?.startup?.promise) await window.MathJax.startup.promise;
    if (window.MathJax?.typesetPromise) await window.MathJax.typesetPromise([ui['result-detail']]);
    document.documentElement.dataset.resultMathReady = 'true';
  });
}

function proofScopeText(route) {
  if (route === 'bounded-proof') return 'Bounded-weight proof';
  if (route === 'general-proof') return 'General-weight proof';
  if (route && !['all', 'printed proof', 'proof'].includes(route)) return route.replace(/-/g, ' ');
  return '';
}

function connectionList(parent, title, edges, direction) {
  parent.append(element('h3', '', title));
  if (!edges.length) { parent.append(element('p', 'empty-connections', direction === 'from' ? 'No named prerequisite is recorded in this map.' : 'No later use is recorded in this map.')); return; }
  const list = element('ul', 'connection-list');
  const grouped = new Map();
  for (const edge of edges) {
    const otherId = edge[direction];
    if (!grouped.has(otherId)) grouped.set(otherId, []);
    grouped.get(otherId).push(edge);
  }
  for (const [otherId, records] of grouped) {
    const li = element('li');
    const other = results.get(otherId);
    if (other) {
      const button = element('button', 'connection-button'); button.type = 'button';
      button.append(element('span', '', `${statusFor(other).symbol} ${labelFor(other)}`), element('small', '', other.title));
      button.addEventListener('click', () => selectResult(otherId)); li.append(button);
    } else {
      const input = externals.get(otherId);
      const button = element('button', 'connection-button external-connection', input?.title || otherId);
      button.type = 'button'; button.addEventListener('click', () => showExternal(otherId)); li.append(button);
    }
    const reason = records.map(e => e.reader_reason || e.reason).filter(Boolean).filter((r, i, all) => all.indexOf(r) === i).join(' ');
    const evidenceBox = element('details', 'source-notes');
    evidenceBox.append(element('summary', '', 'Why this arrow appears'));
    if (reason) evidenceBox.append(element('p', 'connection-reason', reason));
    const scopes = records.map(e => proofScopeText(e.route)).filter(Boolean).filter((r, i, all) => all.indexOf(r) === i);
    if (scopes.length) evidenceBox.append(element('p', 'source-notes', scopes.join(' · ')));
    const evidence = records.map(evidenceText).filter(Boolean).filter((r, i, all) => all.indexOf(r) === i).join('; ');
    if (evidence) evidenceBox.append(element('p', 'paper-locator', `Use in the paper · ${evidence}`));
    li.append(evidenceBox);
    list.append(li);
  }
  parent.append(list);
}

function showEdge(records) {
  const detail = ui['result-detail']; detail.replaceChildren();
  detail.append(element('p', 'result-label', 'Dependency'), element('h2', '', 'Uses in the written proof'));
  for (const edge of records || []) {
    const from = results.get(edge.from) || externals.get(edge.from);
    const to = results.get(edge.to) || externals.get(edge.to);
    const fromLabel = results.has(edge.from) ? labelFor(from) : from?.title || edge.from;
    const toLabel = results.has(edge.to) ? labelFor(to) : to?.title || edge.to;
    detail.append(element('h3', '', `${fromLabel} → ${toLabel}`));
    if (from?.title) detail.append(element('p', '', from.title));
    if (edge.reader_reason || edge.reason) detail.append(element('p', '', edge.reader_reason || edge.reason));
    const scope = proofScopeText(edge.route);
    if (scope) detail.append(element('p', 'source-notes', scope));
    const evidence = evidenceText(edge);
    if (evidence) detail.append(element('p', 'paper-locator', `Use in the paper · ${evidence}`));
    if (results.has(edge.to)) {
      const button = element('button', '', `Read ${labelFor(to)}`); button.type = 'button';
      button.addEventListener('click', () => selectResult(edge.to)); detail.append(button);
    }
  }
  revealDetail();
  typesetDetail();
}

function renderProofScope(parent, result) {
  const routes = (paper.routes || []).filter(route => route.target === result.id);
  for (const route of routes) {
    parent.append(element('h3', '', 'Proof scope'));
    if (route.note) parent.append(element('p', 'source-notes', route.note));
    if (route.scope_warning) parent.append(element('p', 'source-notes', route.scope_warning));
    for (const presentation of route.presentations || []) {
      parent.append(element('p', 'source-notes', presentation.scope || proofScopeText(presentation.id) || presentation.id));
      const links = element('div', 'connection-list');
      for (const id of presentation.prerequisites || []) {
        const item = results.get(id) || externals.get(id);
        if (!item) continue;
        const button = element('button', 'connection-button', `${results.has(id) ? `${labelFor(item)} · ` : ''}${item.title}`);
        button.type = 'button'; button.addEventListener('click', () => results.has(id) ? selectResult(id) : showExternal(id)); links.append(button);
      }
      parent.append(links);
    }
  }
}

function renderRelationships(parent, result) {
  const relationships = (paper.relationships || []).filter(r => r.from === result.id || r.to === result.id);
  if (!relationships.length) return;
  parent.append(element('h3', '', 'Related formulations and proof reuse'));
  parent.append(element('p', 'source-notes', 'These relationships are separate from prerequisite arrows.'));
  const list = element('ul', 'connection-list');
  for (const relationship of relationships) {
    const otherId = relationship.from === result.id ? relationship.to : relationship.from;
    const other = results.get(otherId); if (!other) continue;
    const li = element('li');
    const button = element('button', 'connection-button', `${labelFor(other)} · ${other.title}`); button.type = 'button';
    button.addEventListener('click', () => selectResult(otherId)); li.append(button);
    if (relationship.why) li.append(element('p', 'connection-reason', relationship.why));
    const where = sourceText(relationship.consumer_lines);
    if (where) li.append(element('p', 'paper-locator', where));
    list.append(li);
  }
  parent.append(list);
}

function showResult(result) {
  const detail = ui['result-detail'];
  window.MathJax?.typesetClear?.([detail]);
  detail.replaceChildren();
  detail.append(element('div', 'result-label', labelFor(result)), element('h2', '', result.title));
  detail.append(element('p', 'result-summary', result.summary || 'See the paper and the formalization guide for this result.'));
  const definitions = [...(paper.common_notation || []), ...(result.definitions || [])];
  if (definitions.length) {
    detail.append(element('h3', '', 'Notation'));
    for (const definition of definitions) detail.append(element('p', 'math-definition', typeof definition === 'string' ? definition : definition.text || definition.definition || ''));
  }
  if (result.statement) {
    detail.append(element('h3', '', 'Statement'));
    for (const paragraph of (Array.isArray(result.statement) ? result.statement : [result.statement])) detail.append(element('p', 'math-statement', paragraph));
  }
  const card = element('div', `coverage-card ${statusFor(result).className}`);
  card.append(statusBadge(result));
  const scope = result.coverage?.scope || (result.coverage?.status === 'not_in_release' ? 'No certificate for this result is included in the release described by this guide.' : 'A matching certificate has not been assessed for this entry.');
  card.append(element('p', '', scope));
  if (result.coverage?.links?.length) {
    const links = element('div', 'certificate-links');
    for (const link of result.coverage.links) addLink(links, link.label || 'Lean certificate', link.url);
    card.append(links);
  }
  detail.append(card);
  const locator = sourceText(result.source);
  if (locator) detail.append(element('p', 'paper-locator', `Paper statement · ${locator}`));
  if (result.note || result.notes) {
    const notes = Array.isArray(result.notes) ? result.notes : [result.note || result.notes];
    for (const note of notes) if (note) detail.append(element('p', 'source-notes', typeof note === 'string' ? note : note.text || note.note || ''));
  }
  const guide = element('p'); addLink(guide, 'Precise certified statements and proof changes', paper.guide); detail.append(guide);
  renderProofScope(detail, result);
  connectionList(detail, 'Uses', (paper.edges || []).filter(e => e.to === result.id), 'from');
  connectionList(detail, 'Used by', (paper.edges || []).filter(e => e.from === result.id), 'to');
  renderRelationships(detail, result);
  typesetDetail();
}

function selectResult(id, { openGroup = true, center = true } = {}) {
  const result = results.get(id); if (!result) return;
  selected = id;
  const group = groupFor.get(id);
  if (openGroup && group && !expanded.has(group)) { expanded.add(group); drawGraph(); }
  showResult(result); graphHighlight(); updateLocation(id);
  revealDetail();
  ui['focus-result'].disabled = false;
  for (const button of ui['result-list'].querySelectorAll('[data-result]')) button.setAttribute('aria-current', String(button.dataset.result === id));
  if (center && cy && visibleIds.has(id)) cy.center(cy.getElementById(visibleIds.get(id)));
  ui['search-results'].hidden = true; ui['result-search'].setAttribute('aria-expanded', 'false');
}

function showExternal(id) {
  const input = externals.get(id);
  const detail = ui['result-detail']; detail.replaceChildren();
  detail.append(element('p', 'result-label', 'External input'), element('h2', '', input?.title || id));
  if (input?.scope || input?.summary) detail.append(element('p', '', input.scope || input.summary));
  if (input?.locator) detail.append(element('p', 'paper-locator', input.locator));
  detail.append(element('p', 'source-notes', 'This input comes from outside the paper. Its presence in the dependence map is separate from the formalization status of the paper’s own results.'));
  connectionList(detail, 'Used by', (paper.edges || []).filter(e => e.from === id), 'to');
  revealDetail();
  typesetDetail();
}

function searchResults() {
  const query = ui['result-search'].value.trim().toLocaleLowerCase();
  const target = ui['search-results']; target.replaceChildren();
  if (!query) { target.hidden = true; ui['result-search'].setAttribute('aria-expanded', 'false'); return; }
  const terms = query.split(/\s+/);
  const matches = paper.results.filter(r => {
    const text = `${labelFor(r)} ${r.title} ${r.id}`.toLocaleLowerCase();
    return terms.every(term => text.includes(term));
  });
  target.hidden = false; ui['result-search'].setAttribute('aria-expanded', 'true');
  if (!matches.length) { target.append(element('p', 'search-empty', 'No matching result. Try its number or a word from its title.')); return; }
  for (const result of matches.slice(0, 20)) {
    const button = element('button', '', `${statusFor(result).symbol} ${labelFor(result)}`); button.type = 'button';
    button.append(element('small', '', result.title));
    button.addEventListener('click', () => selectResult(result.id)); target.append(button);
  }
  if (matches.length > 20) target.append(element('p', 'search-empty', `${matches.length} matches. Add another word to narrow the list.`));
}

async function loadPaper(slug, initialResult) {
  const number = ++loadNumber;
  document.documentElement.dataset.paperMapReady = 'loading';
  ui['graph-summary'].textContent = 'Loading the paper map…';
  ui['graph-error'].hidden = true;
  try {
    const response = await fetch(`graphs/paper-results/${encodeURIComponent(slug)}.json`, { cache: 'no-store' });
    if (!response.ok) throw new Error('The paper data could not be loaded.');
    const data = await response.json();
    if (number !== loadNumber) return;
    if (!Array.isArray(data.results) || !Array.isArray(data.clusters)) throw new Error('This paper map is not available yet.');
    paper = { ...data, slug };
    document.getElementById('bounded-arrow-note').hidden = !(paper.edges || []).some(edge => /bounded/.test(edge.route || ''));
    results = new Map(paper.results.map(r => [r.id, r]));
    externals = new Map((paper.external_inputs || []).map(r => [r.id, r]));
    groups = paper.clusters.map(g => ({ ...g, members: g.members.filter(id => results.has(id)) }));
    groupFor = new Map();
    for (const group of groups) for (const id of group.members) groupFor.set(id, group.id);
    const other = paper.results.filter(r => !groupFor.has(r.id));
    if (other.length) {
      groups.push({ id: 'other-results', title: 'Further results', members: other.map(r => r.id) });
      other.forEach(r => groupFor.set(r.id, 'other-results'));
    }
    expanded = new Set(); selected = null;
    ui['paper-select'].value = slug;
    ui['paper-title'].textContent = paper.title;
    ui['paper-authors'].textContent = (paper.authors || []).join(', ');
    ui['guide-link'].href = paper.guide || 'https://github.com/cjanjigi/LPP#readme';
    document.title = `${paper.title} · Dependence map · LPP`;
    ui['result-search'].value = ''; ui['search-results'].hidden = true;
    ui['result-search'].setAttribute('aria-expanded', 'false');
    ui['focus-result'].disabled = true;
    renderAllResults(); showIntroduction(); drawGraph(); updateLocation(null);
    if (initialResult && results.has(initialResult)) selectResult(initialResult);
  } catch (error) {
    ui['graph-error'].hidden = false;
    ui['graph-error'].textContent = error.message;
    ui['graph-summary'].textContent = 'Paper map unavailable.';
    document.documentElement.dataset.paperMapReady = 'error';
  }
}

ui['paper-select'].addEventListener('change', () => loadPaper(ui['paper-select'].value));
ui['expand-all'].addEventListener('click', () => { expanded = new Set(groups.map(g => g.id)); drawGraph(); });
ui['collapse-all'].addEventListener('click', () => { expanded.clear(); drawGraph(); });
ui['fit-map'].addEventListener('click', () => cy?.fit(undefined, 32));
ui['show-external'].addEventListener('change', () => drawGraph());
ui['zoom-in'].addEventListener('click', () => { if (cy) cy.zoom({ level: Math.min(cy.maxZoom(), cy.zoom() * 1.35), renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 } }); });
ui['zoom-out'].addEventListener('click', () => { if (cy) cy.zoom({ level: Math.max(cy.minZoom(), cy.zoom() / 1.35), renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 } }); });
ui['focus-result'].addEventListener('click', () => {
  if (!cy || !selected || !visibleIds.has(selected)) return;
  cy.fit(cy.getElementById(visibleIds.get(selected)).closedNeighborhood(), 60);
});
ui['result-search'].addEventListener('input', () => { if (paper) searchResults(); });
ui['result-search'].addEventListener('keydown', event => {
  if (event.key === 'Escape') { ui['search-results'].hidden = true; ui['result-search'].setAttribute('aria-expanded', 'false'); }
  if (event.key === 'ArrowDown' || event.key === 'Enter') {
    const first = ui['search-results'].querySelector('button');
    if (first && !ui['search-results'].hidden) { event.preventDefault(); if (event.key === 'Enter') first.click(); else first.focus(); }
  }
});
document.addEventListener('click', event => {
  if (!event.target.closest('.search-wrap')) { ui['search-results'].hidden = true; ui['result-search'].setAttribute('aria-expanded', 'false'); }
});
const initial = new URL(location.href);
const initialSlug = initial.searchParams.get('paper');
const allowedSlugs = Array.from(ui['paper-select'].options, option => option.value);
loadPaper(allowedSlugs.includes(initialSlug) ? initialSlug : 'differentiability', initial.searchParams.get('result'));
