/* Protect TeX from Markdown's own escape and emphasis rules. JSON graph data
   keeps ordinary TeX; use this only when serializing GitHub Markdown. */
export function githubMath(markdown) {
  let fence = null;
  let display = null;
  return String(markdown).split('\n').map(line => {
    if (fence) {
      if (new RegExp(`^[ \\t]*${fence.character}{${fence.length},}[ \\t]*$`).test(line)) fence = null;
      return line;
    }
    if (display !== null) {
      if (/^\s*\$\$\s*$/.test(line)) {
        const indent = display;
        display = null;
        return indent + '```';
      }
      return line;
    }
    const startFence = /^([ \t]*)(`{3,}|~{3,})(.*)$/.exec(line);
    if (startFence) {
      fence = { character: startFence[2][0], length: startFence[2].length };
      return line;
    }
    const startDisplay = /^(\s*)\$\$\s*$/.exec(line);
    if (startDisplay) {
      display = startDisplay[1];
      return display + '```math';
    }
    return protectInline(line);
  }).join('\n');
}

function escaped(text, index) {
  let count = 0;
  for (let i = index - 1; i >= 0 && text[i] === '\\'; i--) count++;
  return count % 2 === 1;
}

function protectInline(line) {
  let out = '';
  for (let i = 0; i < line.length;) {
    // An existing protected expression is already in GitHub's preferred form.
    if (line.startsWith('$`', i) && !escaped(line, i)) {
      const end = line.indexOf('`$', i + 2);
      if (end !== -1) {
        out += line.slice(i, end + 2);
        i = end + 2;
        continue;
      }
    }
    // Inline code may contain dollar signs that are examples rather than math.
    if (line[i] === '`' && !escaped(line, i)) {
      const run = /^`+/.exec(line.slice(i))[0];
      let end = line.indexOf(run, i + run.length);
      while (end !== -1 && (line[end - 1] === '`' || line[end + run.length] === '`')) end = line.indexOf(run, end + run.length);
      if (end !== -1) {
        out += line.slice(i, end + run.length);
        i = end + run.length;
        continue;
      }
    }
    if (line[i] === '$' && !escaped(line, i) && line[i - 1] !== '$' && line[i + 1] !== '$') {
      let end = i + 1;
      while (end < line.length && (line[end] !== '$' || escaped(line, end))) end++;
      if (end < line.length && line[end + 1] !== '$') {
        const tex = line.slice(i + 1, end);
        if (tex.includes('`')) throw new Error('Inline mathematics contains a backtick; choose an explicit GitHub math delimiter.');
        out += '$`' + tex + '`$';
        i = end + 1;
        continue;
      }
    }
    out += line[i++];
  }
  return out;
}
