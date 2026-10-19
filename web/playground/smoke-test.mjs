import fs from "node:fs";
import init, { infer, run } from "./src/wasm/yulang_wasm.js";

await init({ module_or_path: fs.readFileSync("./src/wasm/yulang_wasm_bg.wasm") });

const ordinary = run("my identity x = x\nmy main = identity 7", "main", 10_000);
const handled = run(
  "act io:\n    our tick: int -> int\nmy main = catch io::tick 7 { io::tick(value), _ -> value }",
  "main",
  10_000,
);
const graph = infer("my identity x = x\nmy main = identity 7");

if (ordinary !== "7\n" || handled !== "7\n") {
  throw new Error(`unexpected runtime values: ${JSON.stringify({ ordinary, handled })}`);
}
if (!graph.startsWith("Experimental candidate inference graph")) {
  throw new Error(`unexpected inference output: ${graph.slice(0, 120)}`);
}

console.log("WASM smoke passed: inference, ordinary execution, handled effect.");
