import fs from "node:fs";
import init, { infer, infer_types, run, run_module, run_module_report } from "./src/wasm/yulang_wasm.js";

await init({ module_or_path: fs.readFileSync("./src/wasm/yulang_wasm_bg.wasm") });

const examples = {
  ordinary: ["my identity x = x\nmy main = identity 7", "7\n"],
  capturedInitializer: ["my main = 1 + 2\n", "3\n"],
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
  caseBinder: ["my retain x = case x: value -> value\nmy other = retain \"kept\"\nmy main = retain 7", "7\n"],
  caseResumption: [
    "act io:\n    our tick: int -> int\n    our other: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }\nmy main = relay { case io::tick 0: 9 -> 91, _ -> 17 }",
    "91\n",
  ],
  repeatedChoice: [
    fs.readFileSync("./examples/repeated-choice.yu", "utf8"),
    "23\n",
  ],
  ordinaryIslands: [
    fs.readFileSync("./examples/yulang2-ordinary-islands.yu", "utf8"),
    "8\n",
    "countdown_result",
  ],
};
const polymorphicEscapingClosureSource = fs.readFileSync(
  "./examples/polymorphic-escaping-closure.yu",
  "utf8",
);
const yulang2TypesSource = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
const yulang2ConsoleSource = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
function assertRun(source, definition, expected) {
  const actual = run(source, definition, 100_000);
  if (actual !== expected) {
    throw new Error(`unexpected ${definition} runtime value: ${JSON.stringify(actual)}`);
  }
}
assertRun(polymorphicEscapingClosureSource, "main", "7\n");
assertRun(polymorphicEscapingClosureSource, "bool_result", "true\n");
assertRun(polymorphicEscapingClosureSource, "string_result", '"ok"\n');
const yulang2Source = fs.readFileSync("./examples/yulang2-identity-island.yu", "utf8");
const yulang2DiagnosticExamples = {
  typeMismatch: fs.readFileSync("./examples/yulang2-type-mismatch.yu", "utf8"),
  parameterProvenance: fs.readFileSync("./examples/yulang2-parameter-provenance.yu", "utf8"),
};
const yulang2Definitions = {
  int_identity: "7\n",
  bool_identity: "true\n",
  string_identity: '"ok"\n',
};
const yulang2OrdinaryIslandsSource = fs.readFileSync(
  "./examples/yulang2-ordinary-islands.yu",
  "utf8",
);
const yulang2OrdinaryIslandsDefinitions = {
  int_identity: "7\n",
  bool_identity: "true\n",
  string_identity: '"ok"\n',
  countdown_result: "8\n",
};
const results = Object.fromEntries(
  Object.entries(examples).map(([name, [source, , definition = "main"]]) => [
    name,
    run(source, definition, 100_000),
  ]),
);
const yulang2Results = Object.fromEntries(
  Object.entries(yulang2Definitions).map(([definition, expected]) => [
    definition,
    run(yulang2Source, definition, 100_000),
  ]),
);
const graph = infer("my identity x = x\nmy main = identity 7");
const types = infer_types(yulang2TypesSource);
const typesEvents = JSON.parse(run_module(yulang2TypesSource, 100_000));
const consoleEvents = JSON.parse(run_module(yulang2ConsoleSource, 100_000));
const typesReport = JSON.parse(run_module_report(yulang2TypesSource, 100_000));
const consoleReport = JSON.parse(run_module_report(yulang2ConsoleSource, 100_000));
if (typesReport.types !== types || JSON.stringify(typesReport.events) !== JSON.stringify(typesEvents)) {
  throw new Error("combined Types report must preserve public types and ordered writes");
}
if (JSON.stringify(consoleReport.events) !== JSON.stringify(consoleEvents)) {
  throw new Error("combined Console report must preserve ordered writes");
}
for (const [source, expected] of [
  ['println "standalone"\n', ["standalone\n"]],
  ['my forward message = emit message\nmy emit message = println message\nforward "wrapped"\n', ["wrapped\n"]],
  ['my forward value = emit value\nmy emit value = say value\nforward (3, "text")\n', ["(3, text)\n"]],
]) {
  const report = JSON.parse(run_module_report(source, 100_000));
  if (JSON.stringify(report.events) !== JSON.stringify(expected)) {
    throw new Error("library operator dependencies must survive enclosing function capture");
  }
}
for (const [source, budget, reason] of [
  [yulang2TypesSource, 0, "runtime step budget exhausted"],
  [yulang2DiagnosticExamples.typeMismatch, 100_000, "candidate type conflicts"],
  ['act io:\n    our tick: int -> ()\nprintln "prefix"\nsay: 1 + 2\nio::tick 1', 100_000, "unhandled runtime request"],
]) {
  let rejected = false;
  try { run_module_report(source, budget); } catch (error) { rejected = String(error).includes(reason); }
  if (!rejected) { throw new Error("failed module run must withhold the combined report"); }
}

for (const [name, source] of Object.entries(yulang2DiagnosticExamples)) {
  let rejectedAtCandidateConflict = false;
  try {
    infer(source);
  } catch (error) {
    rejectedAtCandidateConflict = String(error).includes("candidate type conflicts");
  }
  if (!rejectedAtCandidateConflict) {
    throw new Error(`unexpected ${name} outcome: expected candidate type conflict`);
  }
}

for (const [name, [, expected]] of Object.entries(examples)) {
  if (results[name] !== expected) {
    throw new Error(`unexpected ${name} runtime value: ${JSON.stringify(results[name])}`);
  }
}
for (const [definition, expected] of Object.entries(yulang2Definitions)) {
  if (yulang2Results[definition] !== expected) {
    throw new Error(`unexpected ${definition} runtime value: ${JSON.stringify(yulang2Results[definition])}`);
  }
}
for (const [definition, expected] of Object.entries(yulang2OrdinaryIslandsDefinitions)) {
  if (run(yulang2OrdinaryIslandsSource, definition, 100_000) !== expected) {
    throw new Error(`unexpected ordinary-islands ${definition} result`);
  }
}
if (!graph.startsWith("Experimental candidate inference graph")) {
  throw new Error(`unexpected inference output: ${graph.slice(0, 120)}`);
}
for (const expected of ["id: ∀", "answer: int", "name: str", "pair: (int, str)"]) {
  if (!types.includes(expected)) {
    throw new Error(`missing public type ${expected}: ${types}`);
  }
}
if (JSON.stringify(typesEvents) !== JSON.stringify(["(42, Yulang)\n"])) {
  throw new Error(`unexpected Types module writes: ${JSON.stringify(typesEvents)}`);
}
if (JSON.stringify(consoleEvents) !== JSON.stringify(["hello from Yulang\n", "3\n"])) {
  throw new Error(`unexpected Console module writes: ${JSON.stringify(consoleEvents)}`);
}

const shallowNegative =
  "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }\nmy main = relay { case io::tick 0: 9 -> io::tick 8, _ -> 17 }";
let shallowHandlerAbsent = false;
const secondTickStart = shallowNegative.lastIndexOf("io::tick 8");
const payloadStart = secondTickStart + "io::tick ".length;
const secondTickPayloadRange = `${payloadStart}..${payloadStart + 1}`;
try {
  run(shallowNegative, "main", 100_000);
} catch (error) {
  shallowHandlerAbsent = String(error).includes(
    `unhandled runtime request at ${secondTickPayloadRange}`,
  );
}
if (!shallowHandlerAbsent) {
  throw new Error("the resumed Case arm must leave its shallow tick handler absent");
}

console.log(`WASM smoke passed: inference, ${Object.keys(examples).length} execution examples, Types/Console module outputs, three Yulang2 identity definitions, and two Yulang2 diagnostic examples.`);
