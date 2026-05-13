import { mkdirSync } from "node:fs";
import { spawnSync } from "node:child_process";

const deployDir = process.env.YULANG_DEPLOY_DIR;

if (!deployDir) {
  console.error("set YULANG_DEPLOY_DIR");
  process.exit(2);
}

mkdirSync(deployDir, { recursive: true });

run("rsync", ["-a", "--exclude=*.html", "dist/", deployDir]);
run("rsync", ["-a", "--delete-after", "--delay-updates", "dist/", deployDir]);

function run(command, args) {
  const result = spawnSync(command, args, {
    cwd: new URL("..", import.meta.url),
    stdio: "inherit",
  });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}
