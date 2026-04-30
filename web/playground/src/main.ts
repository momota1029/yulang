import init, { colorize, run } from "./wasm/yulang_wasm.js";
import "./style.css";

type Diagnostic = {
  severity: "error";
  message: string;
  start: number;
  end: number;
};

type RunOutput = {
  ok: boolean;
  results: RunResult[];
  types: TypeResult[];
  diagnostics: Diagnostic[];
};

type RunResult = {
  index: number;
  value: string;
};

type TypeResult = {
  name: string;
  ty: string;
};

type HighlightKind =
  | "comment"
  | "keyword"
  | "string"
  | "number"
  | "ident"
  | "symbol";

type HighlightSpan = {
  start: number;
  end: number;
  kind: HighlightKind;
};

type ColorizeOutput = {
  ok: boolean;
  spans: HighlightSpan[];
  diagnostics: Diagnostic[];
};

type Example = {
  label: string;
  source: string;
};

const examples: Example[] = [
  {
    label: "Tour",
    source: `// A compact tour of Yulang's current shape.

use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
`,
  },
  {
    label: "Struct",
    source: `// Attach a method to a struct with with:.

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
`,
  },
  {
    label: "Optional Args",
    source: `// Record pattern defaults act like optional named arguments.

my area({width = 1, height = 2}) = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
`,
  },
  {
    label: "References",
    source: `// References are explicit: $x reads, &x = value writes.

{
    my $x = 10
    &x = $x + 1
    $x
}
`,
  },
  {
    label: "List Update",
    source: `// A list element can be updated through a child reference.

{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
`,
  },
  {
    label: "Sub Return",
    source: `// sub: catches return and turns early exit into a value.

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
`,
  },
  {
    label: "Nondet List",
    source: `// each chooses values. .list collects every result.

use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).list
`,
  },
  {
    label: "Nondet Once",
    source: `// .once returns the first useful result as opt.

use std::undet::*

({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
`,
  },
  {
    label: "Junction",
    source: `// all and any make if conditions effectful.

if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
`,
  },
  {
    label: "Types",
    source: `// our and pub bindings are shown in the Types pane.

our twice x = x + x
pub answer = twice 21

answer
`,
  },
];

const sourceInput = document.querySelector<HTMLTextAreaElement>("#source");
const runButton = document.querySelector<HTMLButtonElement>("#run-button");
const result = document.querySelector<HTMLPreElement>("#result");
const types = document.querySelector<HTMLPreElement>("#types");
const exampleButtons = document.querySelector<HTMLDivElement>("#example-buttons");
const editorSurface = document.querySelector<HTMLDivElement>(".editor-surface");
const editorHighlight =
  document.querySelector<HTMLPreElement>("#editor-highlight");
const editorHighlightContent = document.querySelector<HTMLElement>(
  "#editor-highlight-content",
);

if (
  !sourceInput ||
  !runButton ||
  !result ||
  !types ||
  !exampleButtons ||
  !editorSurface ||
  !editorHighlight ||
  !editorHighlightContent
) {
  throw new Error("playground DOM is incomplete");
}

let pendingRenderColor = 0;
let activeExampleIndex = 0;

await init();

setupExampleButtons();
loadExample(0);
renderColor();
runSource();

const editorRenderEvents = [
  "beforeinput",
  "input",
  "change",
  "keydown",
  "keyup",
  "compositionupdate",
  "compositionend",
  "cut",
  "paste",
  "drop",
] as const;

for (const eventName of editorRenderEvents) {
  sourceInput.addEventListener(eventName, scheduleRenderColor);
}
sourceInput.addEventListener("scroll", keepSourceScrollAtOrigin);
window.addEventListener("resize", syncEditorLayout);
runButton.addEventListener("click", runSource);

function setupExampleButtons(): void {
  examples.forEach((example, index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "example-button";
    button.textContent = example.label;
    button.addEventListener("click", () => {
      loadExample(index);
      renderColor();
      runSource();
      sourceInput.focus();
    });
    exampleButtons.append(button);
  });
  updateExampleButtonState();
}

function loadExample(index: number): void {
  activeExampleIndex = index;
  sourceInput.value = examples[index].source;
  editorSurface.scrollTop = 0;
  editorSurface.scrollLeft = 0;
  keepSourceScrollAtOrigin();
  updateExampleButtonState();
}

function updateExampleButtonState(): void {
  exampleButtons.querySelectorAll("button").forEach((button, index) => {
    button.classList.toggle("is-active", index === activeExampleIndex);
  });
}

function runSource(): void {
  const output = run(sourceInput.value) as RunOutput;
  result.classList.toggle("is-error", !output.ok);
  types.classList.toggle("is-error", !output.ok);
  if (output.ok) {
    result.textContent = formatResults(output.results);
    types.textContent = formatTypes(output.types);
  } else {
    result.textContent = output.diagnostics.map(formatDiagnostic).join("\n");
    types.textContent = "";
  }
}

function formatResults(results: RunResult[]): string {
  if (results.length === 0) {
    return "(no output)";
  }
  return results
    .map((item) => `Result ${item.index + 1}: ${item.value}`)
    .join("\n");
}

function formatTypes(types: TypeResult[]): string {
  if (types.length === 0) {
    return "(no exported types)";
  }
  return types.map((item) => `${item.name}: ${item.ty}`).join("\n");
}

function scheduleRenderColor(): void {
  if (pendingRenderColor !== 0) {
    return;
  }
  pendingRenderColor = window.requestAnimationFrame(() => {
    pendingRenderColor = 0;
    renderColor();
  });
}

function renderColor(): void {
  const output = colorize(sourceInput.value) as ColorizeOutput;
  editorHighlightContent.innerHTML = highlightSource(
    sourceInput.value,
    output.spans,
  );
  syncEditorLayout();
}

function syncEditorLayout(): void {
  sourceInput.style.width = "100%";
  sourceInput.style.height = "auto";
  editorHighlight.style.width = "100%";
  editorHighlight.style.minHeight = "100%";

  const width = Math.max(
    editorSurface.clientWidth,
    sourceInput.scrollWidth,
    editorHighlight.scrollWidth,
  );
  sourceInput.style.width = `${width}px`;
  editorHighlight.style.width = `${width}px`;

  const height = Math.max(
    editorSurface.clientHeight,
    sourceInput.scrollHeight,
    editorHighlight.scrollHeight,
  );
  sourceInput.style.height = `${height}px`;
  editorHighlight.style.minHeight = `${height}px`;
  keepSourceScrollAtOrigin();
}

function keepSourceScrollAtOrigin(): void {
  sourceInput.scrollTop = 0;
  sourceInput.scrollLeft = 0;
}

function highlightSource(source: string, spans: HighlightSpan[]): string {
  let cursor = 0;
  let html = "";
  for (const span of spans) {
    if (span.start < cursor) {
      continue;
    }
    html += escapeHtml(source.slice(cursor, span.start));
    html += `<span class="tok tok-${span.kind}">${escapeHtml(
      source.slice(span.start, span.end),
    )}</span>`;
    cursor = span.end;
  }
  html += escapeHtml(source.slice(cursor));
  if (source.endsWith("\n")) {
    html += " ";
  }
  return html;
}

function formatDiagnostic(diagnostic: Diagnostic): string {
  return `${diagnostic.severity}: ${diagnostic.message}`;
}

function escapeHtml(text: string): string {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}
