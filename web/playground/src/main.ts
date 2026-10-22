import init, { infer_types, run, run_module_report } from "./wasm/yulang_wasm.js";
import "./style.css";
import yulang2TupleArity from "../examples/yulang2-tuple-arity.yu?raw";
import yulang2Effects from "../examples/yulang2-effects.yu?raw";
import yulang2IdentityIsland from "../examples/yulang2-identity-island.yu?raw";
import yulang2TypeMismatch from "../examples/yulang2-type-mismatch.yu?raw";
import yulang2ParameterProvenance from "../examples/yulang2-parameter-provenance.yu?raw";
import yulang2OrdinaryIslands from "../examples/yulang2-ordinary-islands.yu?raw";
import repeatedChoice from "../examples/repeated-choice.yu?raw";
import polymorphicEscapingClosure from "../examples/polymorphic-escaping-closure.yu?raw";

const yulang2Types = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
const yulang2Console = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";

const examples: Record<string, string> = {
  yulang2_types: yulang2Types,
  yulang2_console: yulang2Console,
  yulang2_effects: yulang2Effects,
  yulang2_tuple_arity: yulang2TupleArity,
  yulang2_identity_island: yulang2IdentityIsland,
  yulang2_type_mismatch: yulang2TypeMismatch,
  yulang2_parameter_provenance: yulang2ParameterProvenance,
  yulang2_ordinary_islands: yulang2OrdinaryIslands,
  repeated_choice: repeatedChoice,
  polymorphic_escaping_closure: polymorphicEscapingClosure,
  ordinary: "my identity x = x\nmy main = identity 7",
  closure: "my make x = \\y -> x\nmy main = make 12 7",
  recursion: "my loop condition = if condition: loop false else: 11\nmy main = loop true",
  module_expression: "99\nmy main = 7",
  effects:
    "act io:\n    our tick: int -> int\nmy main = catch io::tick 7 { io::tick(value), _ -> value }",
  continuation:
    "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 11 }\nmy main = relay(io::tick 7)",
  nested_receiver:
    "act io:\n    our tick: int -> int\nmy main = catch (catch io::tick 7 { io::tick(value), _ -> value }) { io::tick(value), _ -> value }",
  conditional: "my choose condition yes no = if condition: yes else: no\nmy main = choose true 7 9",
  case: "my classify x = case x: 2 -> 22, _ -> 0\nmy main = classify 2",
  case_binder: "my retain x = case x: value -> value\nmy other = retain \"kept\"\nmy main = retain 7",
  case_resumption:
    "act io:\n    our tick: int -> int\n    our other: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }\nmy main = relay { case io::tick 0: 9 -> 91, _ -> 17 }",
  case_shallow_handler_absent:
    "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }\nmy main = relay { case io::tick 0: 9 -> io::tick 8, _ -> 17 }",
};

const source = document.querySelector<HTMLTextAreaElement>("#source")!;
const definition = document.querySelector<HTMLInputElement>("#definition")!;
const output = document.querySelector<HTMLElement>("#output")!;
const title = document.querySelector<HTMLElement>("#output-title")!;
const status = document.querySelector<HTMLElement>("#status")!;
const inferButton = document.querySelector<HTMLButtonElement>("#infer")!;
const runButton = document.querySelector<HTMLButtonElement>("#run")!;
const definitionLabel = definition.closest("label")!;

source.value = examples.yulang2_types;
definitionLabel.hidden = true;
definition.value = "";

function showResult(label: string, value: string, failed = false): void {
  title.textContent = label;
  status.textContent = failed ? "needs attention" : "complete";
  status.classList.toggle("error", failed);
  output.textContent = value;
}

async function withBusy(label: string, action: () => string): Promise<void> {
  inferButton.disabled = true;
  runButton.disabled = true;
  try {
    await init();
    showResult(label, action());
  } catch (error) {
    showResult("Could not complete", String(error), true);
  } finally {
    inferButton.disabled = false;
    runButton.disabled = false;
  }
}

document.querySelector<HTMLSelectElement>("#example")!.addEventListener("change", (event) => {
  const selected = (event.currentTarget as HTMLSelectElement).value;
  source.value = examples[selected] ?? examples.ordinary;
  const wholeModule = selected === "yulang2_types" || selected === "yulang2_console" || selected === "yulang2_effects" || selected === "yulang2_tuple_arity";
  definitionLabel.hidden = wholeModule;
  definition.value = wholeModule ? "" : selected === "yulang2_identity_island"
    ? "int_identity"
    : selected === "yulang2_ordinary_islands"
      ? "countdown_result"
      : "main";
});

inferButton.addEventListener("click", () => {
  void withBusy("Candidate types and effects", () => infer_types(source.value));
});

runButton.addEventListener("click", () => {
  const selected = document.querySelector<HTMLSelectElement>("#example")!.value;
  if (selected === "yulang2_types" || selected === "yulang2_console" || selected === "yulang2_effects" || selected === "yulang2_tuple_arity") {
    void withBusy("Module types and output", () => {
      const report = JSON.parse(run_module_report(source.value, 100_000)) as {
        types: string;
        events: string[];
      };
      const events = report.events.map((payload, index) => `${index + 1}: ${JSON.stringify(payload)}`).join("\n");
      return `${report.types}\nOutput events\n${events}`;
    });
  } else {
    void withBusy("Runtime result", () => run(source.value, definition.value.trim() || "main", 100_000));
  }
});
