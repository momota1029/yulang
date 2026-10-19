import init, { infer, run } from "./wasm/yulang_wasm.js";
import "./style.css";

const examples: Record<string, string> = {
  ordinary: "my identity x = x\nmy main = identity 7",
  effects:
    "act io:\n    our tick: int -> int\nmy main = catch io::tick 7 { io::tick(value), _ -> value }",
  conditional: "my choose condition yes no = if condition: yes else: no\nmy main = choose true 7 9",
};

const source = document.querySelector<HTMLTextAreaElement>("#source")!;
const definition = document.querySelector<HTMLInputElement>("#definition")!;
const output = document.querySelector<HTMLElement>("#output")!;
const title = document.querySelector<HTMLElement>("#output-title")!;
const status = document.querySelector<HTMLElement>("#status")!;
const inferButton = document.querySelector<HTMLButtonElement>("#infer")!;
const runButton = document.querySelector<HTMLButtonElement>("#run")!;

source.value = examples.ordinary;

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
});

inferButton.addEventListener("click", () => {
  void withBusy(() => infer(source.value));
});

runButton.addEventListener("click", () => {
  void withBusy(() => run(source.value, definition.value.trim() || "main", 100_000));
});
