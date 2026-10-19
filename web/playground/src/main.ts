import init, { infer, run } from "./wasm/yulang_wasm.js";
import "./style.css";
import yulang2IdentityIsland from "../examples/yulang2-identity-island.yu?raw";
import repeatedChoice from "../examples/repeated-choice.yu?raw";

const examples: Record<string, string> = {
  yulang2_identity_island: yulang2IdentityIsland,
  repeated_choice: repeatedChoice,
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

source.value = examples.yulang2_identity_island;

function showResult(label: string, value: string, failed = false): void {
  title.textContent = label;
  status.textContent = failed ? "needs attention" : "complete";
  status.classList.toggle("error", failed);
  output.textContent = value;
}

async function withBusy(action: () => string): Promise<void> {
  inferButton.disabled = true;
  runButton.disabled = true;
  try {
    await init();
    showResult("Result", action());
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
  definition.value = selected === "yulang2_identity_island" ? "int_identity" : "main";
});

inferButton.addEventListener("click", () => {
  void withBusy(() => infer(source.value));
});

runButton.addEventListener("click", () => {
  void withBusy(() => run(source.value, definition.value.trim() || "main", 100_000));
});
