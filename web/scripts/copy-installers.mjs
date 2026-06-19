import { copyFile, mkdir } from "node:fs/promises";

const repoRoot = new URL("../../", import.meta.url);
const webOutDir = new URL("../dist/", import.meta.url);

await mkdir(webOutDir, { recursive: true });
await Promise.all([
  copyFile(new URL("scripts/install.sh", repoRoot), new URL("install.sh", webOutDir)),
  copyFile(new URL("scripts/install.ps1", repoRoot), new URL("install.ps1", webOutDir)),
]);
