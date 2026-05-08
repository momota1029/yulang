import { createHash } from "node:crypto";
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";

const docsOutDir = new URL("../../dist/docs/", import.meta.url);
const assetsDir = new URL("assets/", docsOutDir);

await mkdir(assetsDir, { recursive: true });
await externalizeInlineScripts(docsOutDir);
await externalizeCssDataSvgs(assetsDir);
await writeDocsIndexRedirect();

async function externalizeInlineScripts(dirUrl) {
  const entries = await readdir(dirUrl, { withFileTypes: true });
  for (const entry of entries) {
    const entryUrl = new URL(entry.name, dirUrl);
    if (entry.isDirectory()) {
      await externalizeInlineScripts(new URL(`${entry.name}/`, dirUrl));
      continue;
    }
    if (entry.isFile() && entry.name.endsWith(".html")) {
      await externalizeHtmlScripts(entryUrl);
    }
  }
}

async function externalizeHtmlScripts(htmlUrl) {
  const html = await readFile(htmlUrl, "utf8");
  let changed = false;
  const writes = [];
  const next = html.replace(
    /<script([^>]*)>([\s\S]*?)<\/script>/g,
    (match, attrs, body) => {
      if (/\ssrc\s*=/.test(attrs) || body.trim().length === 0) {
        return match;
      }
      changed = true;
      const name = inlineScriptName(body);
      writes.push(writeFile(new URL(name, assetsDir), body, "utf8"));
      return `<script${attrs} src="/docs/assets/${name}"></script>`;
    },
  );

  if (!changed) {
    return;
  }
  await Promise.all(writes);
  await writeFile(htmlUrl, next, "utf8");
}

function inlineScriptName(body) {
  const hash = createHash("sha256").update(body).digest("hex").slice(0, 16);
  return `inline-${hash}.js`;
}

async function externalizeCssDataSvgs(dirUrl) {
  const entries = await readdir(dirUrl, { withFileTypes: true });
  for (const entry of entries) {
    const entryUrl = new URL(entry.name, dirUrl);
    if (entry.isDirectory()) {
      await externalizeCssDataSvgs(new URL(`${entry.name}/`, dirUrl));
      continue;
    }
    if (entry.isFile() && entry.name.endsWith(".css")) {
      await externalizeCssFileDataSvgs(entryUrl);
    }
  }
}

async function externalizeCssFileDataSvgs(cssUrl) {
  const css = await readFile(cssUrl, "utf8");
  const writes = [];
  let changed = false;
  const next = css.replace(
    /url\("data:image\/svg\+xml,([^"]+)"\)|url\('data:image\/svg\+xml,([^']+)'\)/g,
    (match, doubleQuoted, singleQuoted) => {
      const encoded = doubleQuoted ?? singleQuoted;
      const quote = doubleQuoted === undefined ? "'" : '"';
      const svg = decodeURIComponent(encoded);
      const name = svgAssetName(svg);
      writes.push(writeFile(new URL(name, assetsDir), svg, "utf8"));
      changed = true;
      return `url(${quote}/docs/assets/${name}${quote})`;
    },
  );

  if (!changed) {
    return;
  }
  await Promise.all(writes);
  await writeFile(cssUrl, next, "utf8");
}

function svgAssetName(svg) {
  const hash = createHash("sha256").update(svg).digest("hex").slice(0, 16);
  return `icon-${hash}.svg`;
}

async function writeDocsIndexRedirect() {
  await writeFile(
    new URL("index.html", docsOutDir),
    `<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width,initial-scale=1">
    <meta http-equiv="refresh" content="0; url=/docs/guide/">
    <link rel="canonical" href="/docs/guide/">
    <title>Yulang Docs</title>
  </head>
  <body>
    <main>
      <p>Redirecting to <a href="/docs/guide/">Yulang Guide</a>.</p>
    </main>
  </body>
</html>
`,
    "utf8",
  );
}
