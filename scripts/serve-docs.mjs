import http from 'node:http';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const docsRoot = await fs.realpath(path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../docs'));
const port = Number(process.env.LPP_DOCS_PORT ?? 4173);
if (!Number.isInteger(port) || port < 0 || port > 65535) {
  throw new Error('LPP_DOCS_PORT must be an integer from 0 to 65535.');
}

const contentTypes = new Map([
  ['.html', 'text/html; charset=utf-8'],
  ['.js', 'text/javascript; charset=utf-8'],
  ['.css', 'text/css; charset=utf-8'],
  ['.json', 'application/json; charset=utf-8'],
  ['.md', 'text/plain; charset=utf-8']
]);
const withinDocs = file => file.startsWith(docsRoot + path.sep);

const server = http.createServer(async (request, response) => {
  if (request.method !== 'GET' && request.method !== 'HEAD') {
    response.writeHead(405, { Allow: 'GET, HEAD' }).end('Method not allowed');
    return;
  }
  let pathname;
  try {
    pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
  } catch {
    response.writeHead(400).end('Invalid path');
    return;
  }
  if (pathname === '/') pathname = '/paper-map.html';
  const requestedFile = path.resolve(docsRoot, '.' + pathname);
  const contentType = contentTypes.get(path.extname(requestedFile));
  if (!withinDocs(requestedFile) || !contentType) {
    response.writeHead(404).end('Not found');
    return;
  }
  try {
    const file = await fs.realpath(requestedFile);
    if (!withinDocs(file)) {
      response.writeHead(404).end('Not found');
      return;
    }
    const content = await fs.readFile(file);
    response.writeHead(200, {
      'Content-Type': contentType,
      'Content-Length': content.length,
      'Cache-Control': 'no-store',
      'X-Content-Type-Options': 'nosniff'
    });
    response.end(request.method === 'HEAD' ? undefined : content);
  } catch (error) {
    response.writeHead(['ENOENT', 'ENOTDIR', 'EISDIR'].includes(error.code) ? 404 : 500).end('Not found');
  }
});

server.on('error', error => {
  console.error(error.code === 'EADDRINUSE'
    ? 'The documentation port is in use. Choose another with LPP_DOCS_PORT.'
    : `Could not start the documentation server (${error.code || 'unknown error'}).`);
  process.exitCode = 1;
});
server.listen(port, '127.0.0.1', () => {
  console.log(`LPP documentation: http://127.0.0.1:${server.address().port}/`);
});
