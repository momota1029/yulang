import { copyFile, mkdir } from "node:fs/promises";

const repoRoot = new URL("../../", import.meta.url);
const webOutDir = new URL("../dist/", import.meta.url);

await mkdir(webOutDir, { recursive: true });
await Promise.all([
  copyFile(new URL("scripts/install.sh", repoRoot), new URL("install.sh", webOutDir)),
  copyFile(new URL("scripts/install.ps1", repoRoot), new URL("install.ps1", webOutDir)),
  copyFile(new URL("scripts/uninstall.sh", repoRoot), new URL("uninstall.sh", webOutDir)),
  copyFile(new URL("scripts/uninstall.ps1", repoRoot), new URL("uninstall.ps1", webOutDir)),
]);
