import { createHash } from "node:crypto";
import {
  copyFile,
  cp,
  mkdir,
  readFile,
  readdir,
  rm,
  writeFile,
} from "node:fs/promises";

const docsOutDir = new URL("../../dist-docs/", import.meta.url);
const webOutDir = new URL("../../dist/", import.meta.url);
const assetsDir = new URL("assets/", docsOutDir);

await mkdir(assetsDir, { recursive: true });
await externalizeInlineScripts(docsOutDir);
await externalizeCssDataSvgs(assetsDir);
await mergeDocsOutput();
await createCleanUrlIndexes(webOutDir);

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
      return `<script${attrs} src="/assets/${name}"></script>`;
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
      return `url(${quote}/assets/${name}${quote})`;
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

async function mergeDocsOutput() {
  await mkdir(webOutDir, { recursive: true });
  await cp(docsOutDir, webOutDir, { recursive: true, force: true });
  await rm(docsOutDir, { recursive: true, force: true });
}

async function createCleanUrlIndexes(dirUrl) {
  const entries = await readdir(dirUrl, { withFileTypes: true });
  for (const entry of entries) {
    const entryUrl = new URL(entry.name, dirUrl);
    if (entry.isDirectory()) {
      await createCleanUrlIndexes(new URL(`${entry.name}/`, dirUrl));
      continue;
    }
    if (!shouldCreateCleanUrlIndex(entry.name)) {
      continue;
    }
    const cleanDir = new URL(
      `${entry.name.slice(0, -".html".length)}/`,
      dirUrl,
    );
    await mkdir(cleanDir, { recursive: true });
    await copyFile(entryUrl, new URL("index.html", cleanDir));
  }
}

function shouldCreateCleanUrlIndex(filename) {
  return (
    filename.endsWith(".html") &&
    filename !== "index.html" &&
    filename !== "404.html"
  );
}
