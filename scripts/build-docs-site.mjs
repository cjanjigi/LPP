import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

if (process.argv.length !== 3) {
  throw new Error('Usage: node scripts/build-docs-site.mjs EMPTY_OUTPUT_DIRECTORY');
}

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const requested = path.resolve(process.argv[2]);
const parent = await fs.realpath(path.dirname(requested));
const output = path.join(parent, path.basename(requested));
for (let ancestor = parent; ; ancestor = path.dirname(ancestor)) {
  try {
    await fs.lstat(path.join(ancestor, '.git'));
    throw new Error('Build the public site outside every Git checkout.');
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
  }
  if (ancestor === path.dirname(ancestor)) break;
}
try {
  await fs.mkdir(output);
} catch (error) {
  if (error.code !== 'EEXIST') throw error;
}
if (!(await fs.lstat(output)).isDirectory() || (await fs.readdir(output)).length) {
  throw new Error('The public site output must be an empty directory.');
}

// Publish only the viewer and its data, with a copy of the project license.
const papers = ['strong-existence', 'differentiability', 'martin-2004', 'bk-1985', 'liggett-1985'];
const copies = [
  ['docs/paper-map.html', 'index.html'],
  ['docs/paper-map.html', 'paper-map.html'],
  ['docs/assets/paper-map.css', 'assets/paper-map.css'],
  ['docs/assets/paper-map.js', 'assets/paper-map.js'],
  ['LICENSE', 'LICENSE'],
  ...papers.map(slug => [`docs/graphs/paper-results/${slug}.json`, `graphs/paper-results/${slug}.json`])
];
for (const [source, destination] of copies) {
  const sourcePath = path.join(root, source);
  if (!(await fs.lstat(sourcePath)).isFile()) throw new Error(`Expected a regular source file: ${source}`);
  const target = path.join(output, destination);
  await fs.mkdir(path.dirname(target), { recursive: true });
  await fs.copyFile(sourcePath, target);
}
await fs.writeFile(path.join(output, '.nojekyll'), '');
console.log(JSON.stringify({ files: [...copies.map(([, destination]) => destination), '.nojekyll'].sort(), papers }, null, 2));
