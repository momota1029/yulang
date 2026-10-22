import fs from "node:fs";
import init, { infer, infer_types, run, run_module, run_module_report } from "./src/wasm/yulang_wasm.js";

await init({ module_or_path: fs.readFileSync("./src/wasm/yulang_wasm_bg.wasm") });

const examples = {
  generatedStringConcat: ['my main = "a%{7}b%{8}c"', '"a7b8c"\n'],
  genericStringConcat: ['my f text = "<%{text}>"; my main = (f 7, f "a")', '("<7>", "<a>")\n'],
  orderedStringConcat: ['my main = say: "a%{say: 1; 7}b%{say: 2; 8}c"', '1\n2\na7b8c\n'],
  generatedInterpolation: ['my main = "%{7}"', '"7"\n'],
  polymorphicInterpolation: ['my f text = "%{text}"; my main = (f 7, f "a")', '("7", "a")\n'],
  effectfulInterpolation: ['my main = say: "%{say: 3; 7}"', '3\n7\n'],
  resumedRecord: ["act io:\n    our tick: int -> int\nmy relay(thunk:[io] 'a) = catch thunk { io::tick(p), k -> { my first = k 11; k 23 } }\nmy main = relay { first: io::tick 0, second: true }", '{first: 23, second: true}\n'],
  emptyRecord: ['my main = {}', '{}\n'],
  namedRecord: ['my main = { width: 3, height: 4 }', '{width: 3, height: 4}\n'],
  polymorphicRecord: ['my make x = { value: x }; my main = (make 7, make "s")', '({value: 7}, {value: "s"})\n'],
  nestedRecord: ['my id x = x; my main = id { nested: { x: 3 }, empty: {} }', '{nested: {x: 3}, empty: {}}\n'],
  importedSubtraction: ['use std::int::sub\nmy main = sub 7 10', '-3\n'],
  importedAliasProduct: ['use std::int::mul as product\nmy main = product 12 34', '408\n'],
  importedGlobProduct: ['use std::int::*\nmy main = mul 12 34', '408\n'],
  integerSubtraction: ['my main = std::int::sub 7 10', '-3\n'],
  integerMultiplication: ['my main = 2 + 3 * 4', '14\n'],
  integerNegation: ['my main = (-12) * (-34)', '408\n'],
  integerGenericProduct: ['my square x = x * x\nmy main = square 9', '81\n'],
  integerPartialProduct: ['my times_two = std::int::mul 2\nmy main = (times_two 3, times_two 4)', '(6, 8)\n'],
  integerLargeProduct: ['my main = 12345678901234567890 * 12345678901234567890', '152415787532388367501905199875019052100\n'],
  annotatedPair: ['my pair(value:(int,int)) = value\nmy main = pair (1,2)', '(1, 2)\n'],
  annotatedSingleton: ['my f(x:(int,)) = x\nmy main = f (7,)', '(7,)\n'],
  annotatedFunctionProduct: ['my f(x:((int -> int),int)) = case x:\n    (g,n) -> g n\nmy id x = x\nmy main = f (id,7)', '7\n'],
  annotatedRootProduct: ['act io:\n    our tick: int -> int\nmy relay (thunk:[io] (int,int)) = catch thunk { io::tick(p), k -> k p }\nmy main = relay (io::tick 3,4)', '(3, 4)\n'],
  annotatedRootProductDictionary: ['act io:\n    our tick: int -> int\nmy relay(thunk:[io] ((int -> int),int)) = catch thunk { io::tick(p), k -> k p }\nmy add x = x + x\nmy saved = relay (add,io::tick 7)\nmy main = case saved:\n    (f,n) -> f n', '14\n'],
  ordinary: ["my identity x = x\nmy main = identity 7", "7\n"],
  inferredAnnotationHoles: ['my identity: _ -> _ = \\x -> x\nmy main = (identity 7, identity "a")\n', '(7, "a")\n'],
  computationResultHole: ["act io:\n    our tick: int -> int\nmy relay (thunk:[io] _) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my x = io::tick 7; (x, true) }\n", "(11, true)\n"],
  capturedInitializer: ["my main = 1 + 2\n", "3\n"],
  interleavedStatements: ["my main = { 1; my x = 2; 3; x }\n", "2\n"],
  connectedMemberResults: ['my f x = { my first = x.show; my y = x + x; my second = y.show; (first, second, y) }\nmy main = (f 3, f "a")\n', '(("3", "6", 6), ("a", "aa", "aa"))\n'],
  connectedMemberWrites: ['my f x = { say x; my y = x + x; say y; y }\nmy main = (f 3, f "a")\n', '3\n6\na\naa\n'],
  genericComputationMembers: ['act io:\n    our tick: int -> int\nmy compute x = { my before = io::tick 7; x + x }\nmy relay (thunk:[io] \'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = (relay(compute 3), relay(compute "a"))\n', '(6, "aa")\n'],
  genericComputationTuple: ['act io:\n    our tick: int -> int\nmy relay (thunk:[io] \'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; (7, true) }\n', '(7, true)\n'],
  computationFunctionResult: ['act io:\n    our tick: int -> int\nmy relay (thunk:[io] (int -> int)) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; \\x -> x } 7\n', '7\n'],
  genericRepeatedContinuation: ['act io:\n    our tick: int -> int\nmy relay (thunk:[io] \'a) = catch thunk { io::tick(p), k -> { my first = k 11; k 23 } }\nmy main = relay { my x = io::tick 0; (x, true) }\n', '(23, true)\n'],
  statementBranchScopes: ["my main = { my x = 3; { my x = 9; 0; x }; x }\n", "3\n"],
  statementPolymorphicClosure: ['my main = { my add x = x + x; 0; my alias = add; 1; (alias 3, alias "a") }\n', '(6, "aa")\n'],
  statementRepeatedResumption: ["act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> { k 11; k 23 } }\nmy main = relay { 99; io::tick 0; my x = 7; x }\n", "7\n"],
  localMembers: ['my main = { my add x = x + x; my cat x = x + x; (add 3, cat "a") }\n', '(6, "aa")\n'],
  polymorphicLocalMember: ['my main = { my add x = x + x; my alias = add; (alias 3, alias "a") }\n', '(6, "aa")\n'],
  polymorphicCapturedMember: ['my make f = \\x -> f x\nmy add x = x + x\nmy wrapper = make add\nmy main = (wrapper 3, wrapper "a")\n', '(6, "aa")\n'],
  polymorphicRecursiveMember: ['my add x = x + x\nmy loop b x = if b: loop false x else: add x\nmy main = (loop true 3, loop true "a")\n', '(6, "aa")\n'],
  polymorphicMemberWithHandler: ['act io:\n    our tick: int -> int\nmy add x = x + x\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 11 }\nmy main = (add 3, add "a", relay(io::tick 7))\n', '(6, "aa", 11)\n'],
  nestedLocalMember: ["my main = { my outer x = { my add y = y + y; add x }; outer 3 }\n", "6\n"],
  escapingLocalMember: ["my outer ignored = { my add x = x + x; add }\nmy main = outer () 3\n", "6\n"],
  unusedLocalMember: ["my outer x = { my unused y = y + y; x }\nmy main = outer 3\n", "3\n"],
  unusedDirectMember: ["my main = { my unused x = x.show; 7 }\n", "7\n"],
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
  tupleArity: fs.readFileSync("./examples/yulang2-tuple-arity.yu", "utf8"),
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
  [fs.readFileSync("./examples/yulang2-effects.yu", "utf8"), ["42\n"]],
  [fs.readFileSync("./examples/yulang2-named-defaults.yu", "utf8"), ["1\n", "9\n", "12\n"]],
  ['println "standalone"\n', ["standalone\n"]],
  ['use std::int::mul', []],
  ['println "before"\nuse std::int::mul\nsay: mul 3 4\nprintln "after"', ["before\n", "12\n", "after\n"]],
  ['say: ({ println "left"; 3 } * { println "right"; 4 })\n', ["left\n", "right\n", "12\n"]],
  ['my f x = { say x; my y = x + x; say y; y }\n(f 3, f "a")\n', ["3\n", "6\n", "a\n", "aa\n"]],
  ['my f x = { say x; my y = x + x; say y; y }\nmy main = (f 3, f "a")\nmain\n', ["3\n", "6\n", "a\n", "aa\n"]],
  ['my main = { println "a"; my x = { println "init"; 7 }; println "b"; x }\n', ["a\n", "init\n", "b\n"]],
  ['my forward message = emit message\nmy emit message = println message\nforward "wrapped"\n', ["wrapped\n"]],
  ['my forward value = emit value\nmy emit value = say value\nforward (3, "text")\n', ["(3, text)\n"]],
  ['{ my emit x = say x; emit (3, "text") }\n', ["(3, text)\n"]],
  ['my outer x = { my unused = say x; 1 }\nouter 3\nouter 4\n', ["3\n", "4\n"]],
  ['my outer x = { my unused = say x; 1 }\nouter (3, "text")\n', ["(3, text)\n"]],
  ['my outer x = { my unused = say x; 1 }\nouter 3\nouter "text"\nouter (3, "text")\n', ["3\n", "text\n", "(3, text)\n"]],
  ['my add = { my once = println "init"; \\x -> x + x }\nmy main = (add 3, add "a")\n', ["init\n"]],
  ['my main = { my emit x = say x; emit (3, "text") }\n', ["(3, text)\n"]],
  ['my first = { my output = println "first"; 1 }\nmy second = { my output = println "second"; 2 }\nprintln "after"\n', ["first\n", "second\n", "after\n"]],
]) {
  const report = JSON.parse(run_module_report(source, 100_000));
  if (JSON.stringify(report.events) !== JSON.stringify(expected)) {
    throw new Error("library operator dependencies must survive enclosing function capture");
  }
}
for (const [source, budget, reason] of [
  ['use std::missing::*\nmy main = 7', 100_000, 'source imports unavailable'],
  ['use std::int::sub\nmy main = sub true 1', 100_000, 'candidate type conflicts'],
  ['my main = builtin_op::int_mul 12345678901234567890 12345678901234567890', 30, 'runtime step budget exhausted'],
  ['my main = std::int::sub 1 "x"', 100_000, 'candidate type conflicts'],
  ['my main = -true', 100_000, 'candidate type conflicts'],
  [yulang2TypesSource, 0, "runtime step budget exhausted"],
  [yulang2DiagnosticExamples.typeMismatch, 100_000, "candidate type conflicts"],
  [yulang2DiagnosticExamples.tupleArity, 100_000, "lower: Tuple(3), upper: Tuple(2)"],
  ["my identity: _ -> _ = \\x -> x\nmy main:int = identity true\n", 100_000, "candidate type conflicts"],
  ["act io:\n    our tick: int -> int\nmy relay (thunk:[] _) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay(io::tick 7)\n", 100_000, "HandlerEvidence"],
  ['act io:\n    our tick: int -> int\nmy relay (thunk:[] \'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay(io::tick 7)\n', 100_000, "HandlerEvidence"],
  ['act io:\n    our tick: int -> int\nmy outer (thunk:[io] \'a) = \\u -> thunk\nmy saved = outer(io::tick 7)\nmy main = catch saved () { io::tick(p), k -> k 11 }\n', 100_000, "HandlerEvidence"],
  ['act io:\n    our tick: int -> int\nmy receive (thunk:[io] \'a) = thunk\nmy saved = receive(\\u -> io::tick 7)\nmy main = catch saved () { io::tick(p), k -> k 11 }\n', 100_000, "HandlerEvidence"],
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

console.log(`WASM smoke passed: inference, ${Object.keys(examples).length} execution examples, Types/Console/Effects module outputs, three Yulang2 identity definitions, and three Yulang2 diagnostic examples.`);
