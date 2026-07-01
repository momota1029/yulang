import { mkdirSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { join } from "node:path";

const deployDir = process.env.YULANG_DEPLOY_DIR;
const channel = parseChannel(process.argv.slice(2));

if (!deployDir) {
  console.error("set YULANG_DEPLOY_DIR");
  process.exit(2);
}

const targetDir = channel ? join(deployDir, channel) : deployDir;

mkdirSync(targetDir, { recursive: true });

run("rsync", ["-a", "--exclude=*.html", "dist/", targetDir]);
run("rsync", ["-a", "--delete-after", "--delay-updates", "dist/", targetDir]);

function parseChannel(args) {
  let channel = "";
  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index];
    if (arg === "--channel") {
      channel = args[index + 1] ?? "";
      index += 1;
    } else if (arg.startsWith("--channel=")) {
      channel = arg.slice("--channel=".length);
    } else {
      console.error(`unknown deploy-dir option: ${arg}`);
      process.exit(2);
    }
  }
  if (channel && channel !== "stable" && channel !== "nightly") {
    console.error("deploy channel must be stable or nightly");
    process.exit(2);
  }
  return channel;
}

function run(command, args) {
  const result = spawnSync(command, args, {
    cwd: new URL("..", import.meta.url),
    stdio: "inherit",
  });
  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}
