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

type Lang = "ja" | "en";

type Example = {
  label: Record<Lang, string>;
  source: string;
};

type MessageKey =
  | "run"
  | "result"
  | "types"
  | "typesAria"
  | "examples"
  | "examplesLead"
  | "noOutput"
  | "noExportedTypes"
  | "resultLine";

const messages: Record<Lang, Record<MessageKey, string>> = {
  ja: {
    run: "実行",
    result: "結果",
    types: "型",
    typesAria: "型推論",
    examples: "例",
    examplesLead:
      "気になる機能を選ぶと editor に読み込まれて、そのまま実行されます。",
    noOutput: "(出力なし)",
    noExportedTypes: "(公開された型なし)",
    resultLine: "結果",
  },
  en: {
    run: "Run",
    result: "Result",
    types: "Types",
    typesAria: "Type inference",
    examples: "Examples",
    examplesLead:
      "Choose an example to load it into the editor and run it immediately.",
    noOutput: "(no output)",
    noExportedTypes: "(no exported types)",
    resultLine: "Result",
  },
};

const examples: Example[] = [
  {
    label: { ja: "ツアー", en: "Tour" },
    source: `// A compact tour of Yulang's current shape.

use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [
        2
        3
        4
    ]
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
    label: { ja: "構造体", en: "Struct" },
    source: `// Attach a method to a struct with with:.

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
`,
  },
  {
    label: { ja: "省略可能引数", en: "Optional Args" },
    source: `// Record pattern defaults act like optional named arguments.

my area({width = 1, height = 2}) = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
`,
  },
  {
    label: { ja: "参照", en: "References" },
    source: `// References are explicit: $x reads, &x = value writes.

{
    my $x = 10
    &x = $x + 1
    $x
}
`,
  },
  {
    label: { ja: "リスト更新", en: "List Update" },
    source: `// A list element can be updated through a child reference.

{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
`,
  },
  {
    label: { ja: "sub return", en: "Sub Return" },
    source: `// return binds weakly, so its value can live on the next line.

my f() = sub:
    return
        1 + 2 + 3 + 4

f()
`,
  },
  {
    label: { ja: "非決定 list", en: "Nondet List" },
    source: `// each chooses values. .list collects every result.

use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).list
`,
  },
  {
    label: { ja: "非決定 once", en: "Nondet Once" },
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
    label: { ja: "junction", en: "Junction" },
    source: `// all and any make if conditions effectful.

if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
`,
  },
  {
    label: { ja: "型", en: "Types" },
    source: `// our and pub bindings are shown in the Types pane.

our twice x = x + x
pub answer = twice 21

answer
`,
  },
  {
    label: { ja: "effect", en: "Effects" },
    source: `// A handler removes one effect and leaves the others.

act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] _) = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
`,
  },
];

const sourceInput = requireElement<HTMLTextAreaElement>("#source");
const runButton = requireElement<HTMLButtonElement>("#run-button");
const result = requireElement<HTMLPreElement>("#result");
const types = requireElement<HTMLPreElement>("#types");
const exampleButtons = requireElement<HTMLDivElement>("#example-buttons");
const editorSurface = requireElement<HTMLDivElement>(".editor-surface");
const editorHighlight = requireElement<HTMLPreElement>("#editor-highlight");
const editorHighlightContent = requireElement<HTMLElement>(
  "#editor-highlight-content",
);
const languageButtons =
  document.querySelectorAll<HTMLButtonElement>("[data-language-choice]");
const translatableNodes =
  document.querySelectorAll<HTMLElement>("[data-i18n]");
const translatableAriaNodes =
  document.querySelectorAll<HTMLElement>("[data-i18n-aria]");

let pendingRenderColor = 0;
let activeExampleIndex = 0;
let activeLang = resolveInitialLang();
let latestRunOutput: RunOutput | undefined;

setupI18n();

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

function setupI18n(): void {
  languageButtons.forEach((button) => {
    const lang = button.dataset.languageChoice;
    if (lang !== "ja" && lang !== "en") {
      return;
    }
    button.addEventListener("click", () => {
      setLanguage(lang);
    });
  });
  applyLanguage();
}

function setLanguage(lang: Lang): void {
  if (activeLang === lang) {
    return;
  }
  activeLang = lang;
  localStorage.setItem("yulang-playground-lang", lang);
  applyLanguage();
  updateExampleButtonState();
  renderRunOutput();
}

function applyLanguage(): void {
  document.documentElement.lang = activeLang;
  document.documentElement.dataset.lang = activeLang;
  translatableNodes.forEach((node) => {
    const key = node.dataset.i18n;
    if (isMessageKey(key)) {
      node.textContent = t(key);
    }
  });
  translatableAriaNodes.forEach((node) => {
    const key = node.dataset.i18nAria;
    if (isMessageKey(key)) {
      node.setAttribute("aria-label", t(key));
    }
  });
  languageButtons.forEach((button) => {
    const isActive = button.dataset.languageChoice === activeLang;
    button.classList.toggle("is-active", isActive);
    button.setAttribute("aria-pressed", String(isActive));
  });
}

function setupExampleButtons(): void {
  examples.forEach((example, index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "example-button";
    button.textContent = example.label[activeLang];
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
    button.textContent = examples[index].label[activeLang];
    button.classList.toggle("is-active", index === activeExampleIndex);
  });
}

function runSource(): void {
  latestRunOutput = run(sourceInput.value) as RunOutput;
  renderRunOutput();
}

function renderRunOutput(): void {
  if (!latestRunOutput) {
    return;
  }
  const output = latestRunOutput;
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
    return t("noOutput");
  }
  return results
    .map((item) => `${t("resultLine")} ${item.index + 1}: ${item.value}`)
    .join("\n");
}

function formatTypes(types: TypeResult[]): string {
  if (types.length === 0) {
    return t("noExportedTypes");
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

function resolveInitialLang(): Lang {
  const stored = localStorage.getItem("yulang-playground-lang");
  if (stored === "ja" || stored === "en") {
    return stored;
  }
  return navigator.language.toLowerCase().startsWith("ja") ? "ja" : "en";
}

function t(key: MessageKey): string {
  return messages[activeLang][key] ?? messages.en[key];
}

function isMessageKey(key: string | undefined): key is MessageKey {
  return key !== undefined && key in messages.en;
}

function requireElement<T extends Element>(selector: string): T {
  const element = document.querySelector<T>(selector);
  if (!element) {
    throw new Error(`playground DOM is incomplete: ${selector}`);
  }
  return element;
}

function escapeHtml(text: string): string {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}
