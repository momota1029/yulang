import fs from "node:fs";
import init, { infer, run } from "./src/wasm/yulang_wasm.js";

await init({ module_or_path: fs.readFileSync("./src/wasm/yulang_wasm_bg.wasm") });

const examples = {
  ordinary: ["my identity x = x\nmy main = identity 7", "7\n"],
  closure: ["my make x = \\y -> x\nmy main = make 12 7", "12\n"],
  recursion: ["my loop condition = if condition: loop false else: 11\nmy main = loop true", "11\n"],
  moduleExpression: ["99\nmy main = 7", "7\n"],
  handled: [
    "act io:\n    our tick: int -> int\nmy main = catch io::tick 7 { io::tick(value), _ -> value }",
    "7\n",
  ],
  continuation: [
    "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 11 }\nmy main = relay(io::tick 7)",
    "11\n",
  ],
  nestedHandlers: [
    "act io:\n    our tick: int -> int\nmy main = catch (catch io::tick 7 { io::tick(value), _ -> value }) { io::tick(value), _ -> value }",
    "7\n",
  ],
  case: ["my classify x = case x: 2 -> 22, _ -> 0\nmy main = classify 2", "22\n"],
  caseWildcard: ["my classify x = case x: 2 -> 22, _ -> 0\nmy main = classify 3", "0\n"],
};
const results = Object.fromEntries(
  Object.entries(examples).map(([name, [source, expected]]) => [name, run(source, "main", 100_000)]),
);
const graph = infer("my identity x = x\nmy main = identity 7");

for (const [name, [, expected]] of Object.entries(examples)) {
  if (results[name] !== expected) {
    throw new Error(`unexpected ${name} runtime value: ${JSON.stringify(results[name])}`);
  }
}
if (!graph.startsWith("Experimental candidate inference graph")) {
  throw new Error(`unexpected inference output: ${graph.slice(0, 120)}`);
}

console.log(`WASM smoke passed: inference and ${Object.keys(examples).length} execution examples.`);
