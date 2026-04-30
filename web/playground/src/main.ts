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

const initialSource = `// struct methods, references, junctions, and nondeterminism
use std::undet::*

struct point { x: int, y: int } with:
    our pt.norm2: int = pt.x * pt.x + pt.y * pt.y

{
    my chosen = ({
        if all [1, 2, 3] < any [2, 3, 4]:
            each [3, 4, 5]
        else:
            2
    }).once

    case chosen:
        opt::just y ->
            my $current = point { x: 3, y: 2 }
            &current = point { x: 3, y: y }
            $current .norm2
        opt::nil -> 0
}
`;

const sourceInput = document.querySelector<HTMLTextAreaElement>("#source");
const runButton = document.querySelector<HTMLButtonElement>("#run-button");
const result = document.querySelector<HTMLPreElement>("#result");
const types = document.querySelector<HTMLPreElement>("#types");
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
  !editorSurface ||
  !editorHighlight ||
  !editorHighlightContent
) {
  throw new Error("playground DOM is incomplete");
}

await init();

sourceInput.value = initialSource;
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

let pendingRenderColor = 0;

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
