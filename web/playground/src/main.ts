import init, {
    colorize,
    embedded_std_compiled_unit_artifact_status,
} from "./wasm/wasm.js";
import wasmUrl from "./wasm/wasm_bg.wasm?url";
import "./style.css";

redirectCleanDocsPath();

const wasmModuleReady: Promise<WebAssembly.Module> = WebAssembly.compileStreaming(
    fetch(wasmUrl),
);

type Diagnostic = {
    severity: "error";
    code?: string;
    message: string;
    hint?: string;
    start?: number;
    end?: number;
    related: DiagnosticRelated[];
    label?: string;
};

type DiagnosticRelatedOrigin =
    | "type_annotation"
    | "expression"
    | "impl_candidate";

type DiagnosticRelated = {
    message: string;
    start: number;
    end: number;
    origin?: DiagnosticRelatedOrigin;
};

type RunOutput = {
    ok: boolean;
    results: RunResult[];
    stdout: string;
    types: TypeResult[];
    timings?: RunTimings;
    diagnostics: Diagnostic[];
};

type CompletedRun = {
    output: RunOutput;
    source: string;
};

type RunTimings = {
    source_set_ms: number;
    infer_lower_ms: number;
    type_render_ms: number;
    diagnostics_ms: number;
    export_core_ms: number;
    runtime_lower_ms: number;
    monomorphize_ms: number;
    vm_compile_ms: number;
    vm_eval_ms: number;
    total_ms: number;
    files: number;
    entry_files: number;
    std_files: number;
    user_files: number;
    source_cache_hits: number;
    source_cache_misses: number;
    source_cache_clone_ms: number;
    source_cache_build_ms: number;
    compiled_std_artifacts: number;
    compiled_std_runtime_bindings: number;
    compiled_std_cache_hit: boolean;
    compiled_std_fallback_reason?: string;
    vm_eval_expr_calls: number;
    vm_max_eval_depth: number;
    vm_continuation_steps: number;
    vm_max_continuation_frames: number;
};

type EmbeddedStdArtifactsOutput = {
    artifacts: number;
    runtime_bindings: number;
    bytes: number;
    valid: boolean;
    fallback_reason?: string;
};

type WarmupOutput = {
    source_cache_hits: number;
    source_cache_misses: number;
    source_cache_clone_ms: number;
    source_cache_build_ms: number;
    embedded_std_artifacts: number;
    embedded_std_runtime_bindings: number;
    embedded_std_artifacts_bytes: number;
    embedded_std_artifacts_valid: boolean;
    embedded_std_artifacts_fallback_reason?: string;
    total_ms: number;
};

type RunWorkerRequest =
    | {
          id: number;
          kind: "run";
          source: string;
          lang: Lang;
      }
    | {
          id: number;
          kind: "warm-std-cache";
      };

type WorkerRequestTrace = {
    id: number;
    kind: RunWorkerRequest["kind"];
    started_ms: number;
    finished_ms?: number;
    source_chars?: number;
    ok?: boolean;
    continuation_steps?: number;
};

type WorkerDebugContext = {
    worker_age_ms: number;
    handled_requests: number;
    last_started?: WorkerRequestTrace;
    last_completed?: WorkerRequestTrace;
    last_run_used_continuations: boolean;
};

type RunWorkerErrorResponse<Kind extends RunWorkerRequest["kind"]> = {
    id: number;
    kind: Kind;
    ok: false;
    message: string;
    name?: string;
    stack?: string;
    context?: WorkerDebugContext;
};

type RunWorkerResponse =
    | {
          id: number;
          kind: "run";
          ok: true;
          output: RunOutput;
      }
    | {
          id: number;
          kind: "warm-std-cache";
          ok: true;
          output: WarmupOutput;
      }
    | RunWorkerErrorResponse<RunWorkerRequest["kind"]>;

type PendingWorkerRequest = {
    reject: (reason?: unknown) => void;
    resolve: (response: RunWorkerResponse) => void;
};

type RunResponse =
    | Extract<RunWorkerResponse, { kind: "run"; ok: true }>
    | RunWorkerErrorResponse<"run">;
type WarmStdCacheResponse =
    | Extract<RunWorkerResponse, { kind: "warm-std-cache"; ok: true }>
    | RunWorkerErrorResponse<"warm-std-cache">;

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
    | "colon"
    | "delimiter"
    | "function"
    | "keyword"
    | "namespace"
    | "number"
    | "operator"
    | "parameter"
    | "pattern"
    | "property"
    | "string"
    | "type"
    | "type-parameter";

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

type ThemeChoice = "system" | "light" | "dark";

type ResolvedTheme = "light" | "dark";

type Example = {
    label: Record<Lang, string>;
    source: string;
};

type MessageKey =
    | "run"
    | "running"
    | "result"
    | "types"
    | "typesAria"
    | "examples"
    | "noOutput"
    | "noExportedTypes"
    | "notRunYet"
    | "resultLine"
    | "themeSystem"
    | "themeLight"
    | "themeDark";

type DocLinkKey = "guide" | "reference" | "install";

const messages: Record<Lang, Record<MessageKey, string>> = {
    ja: {
        run: "実行",
        running: "実行中",
        result: "評価",
        types: "型",
        typesAria: "型推論",
        examples: "例",
        noOutput: "(出力なし)",
        noExportedTypes: "(公開された型なし)",
        notRunYet: "実行すると結果がここに表示されます。",
        resultLine: "評価",
        themeSystem: "自動",
        themeLight: "ライト",
        themeDark: "ダーク",
    },
    en: {
        run: "Run",
        running: "Running",
        result: "Eval",
        types: "Types",
        typesAria: "Type inference",
        examples: "Examples",
        noOutput: "(no output)",
        noExportedTypes: "(no exported types)",
        notRunYet: "Run the program to show results here.",
        resultLine: "Eval",
        themeSystem: "Auto",
        themeLight: "Light",
        themeDark: "Dark",
    },
};

const docLinks: Record<
    Lang,
    Record<DocLinkKey, { href: string; text: string }>
> = {
    ja: {
        guide: { href: "/ja/guide/", text: "ガイド" },
        reference: { href: "/ja/reference/", text: "リファレンス" },
        install: { href: "/ja/guide/install.html", text: "インストール" },
    },
    en: {
        guide: { href: "/guide/", text: "Guide" },
        reference: { href: "/reference/", text: "Reference" },
        install: { href: "/guide/install.html", text: "Install" },
    },
};

const examples: Example[] = [
    {
        label: { ja: "ツアー", en: "Tour" },
        source: `// === A compact tour of Yulang ===

// methods sit next to the type they extend
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2.say

// nondeterministic search: every Pythagorean triple under 15
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list.say

// junction lifts a comparison over many choices at once
say:
    if all [1, 2, 3] < any [3, 4, 5]:
        "every left dominated"
    else:
        "no"

// symbol variants: ad-hoc tagged choices, matched right inline
my render option = case option:
    :ok msg -> "[ok] " + msg
    :err code -> "[err " + code.show + "]"
    :pending -> "..."

[render(:ok "hello"), render(:err 404), render :pending].say

// a user-defined effect: \`coin\` calls the continuation TWICE,
// so one run explores every branch.
act flip:
    our coin: () -> bool

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

my paths = all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
paths.say
`,
    },
    {
        label: { ja: "文字列マッチ", en: "String Match" },
        source: `// Parser patterns turn strings into structured branches.

use std::text::parse::*

my route line = case line:
    ~"get :key" -> "GET " + key
    ~"set :key {v = ..}" -> "SET " + key + " = " + v
    rule { id = word } if id.starts_with "a" -> "user " + id
    _ -> "unknown"

route "get color" .say
route "set color deep-blue" .say
route "alice" .say
route "???" .say
`,
    },
    {
        label: { ja: "設定ファイル", en: "Config" },
        source: `// Parse a small config string and keep conversions explicit.

my source = "# sample config
port   =   8080

[service]
name=api
workers = 4
"

my c = std::text::config::parse source

my port = case c.get "" "port":
    just text -> text.to_int
    nil -> nil

("port", port).say
("service", c.get "service" "name").say
`,
    },
    {
        label: { ja: "データとメソッド", en: "Data & Methods" },
        source: `// Struct methods live next to the data they extend.

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2.say
`,
    },
    {
        label: { ja: "名前付き既定値", en: "Named Defaults" },
        source: `// Record patterns make named options lightweight.

my box {width = 1, height = width} =
    width * height

box {} .say
box { width: 3 } .say
box { width: 3, height: 4 } .say
`,
    },
    {
        label: { ja: "ボタン", en: "Button" },
        source: `// Symbol variants are lightweight choices with payloads.

my button option = case option:
    :label text -> "<button>%{text}</button>"
    :disabled -> "<button disabled></button>"

say: button: :label "send"
say: button: :disabled
`,
    },
    {
        label: { ja: "局所的な変更", en: "Local Change" },
        source: `// A mutable binding stays local to the surrounding block.

{
    my $total = 0
    for x in 1..5:
        &total = $total + x
    $total
}.say
`,
    },
    {
        label: { ja: "リスト更新", en: "List Update" },
        source: `// Child references make nested updates direct.

{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}.say
`,
    },
    {
        label: { ja: "sub return", en: "Sub Return" },
        source: `// sub gives an expression a local return.

my first_over limit = sub:
    for x in 0..: if x * x > limit: return x
    0

first_over 40 .say
`,
    },
    {
        label: { ja: "callback 衛生性", en: "Callback Hygiene" },
        source: `// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::control::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

my outer = sub:
    my b = g \\i -> if i == 0: return i
    println b.show
    2
outer.say
`,
    },
    {
        label: { ja: "非決定 list", en: "Nondet List" },
        source: `// each branches; .list collects every result.

(each [1, 2, 3] + each [4, 5, 6]).list.say
`,
    },
    {
        label: { ja: "非決定 once", en: "Nondet Once" },
        source: `// Narrow infinite choices as early as possible.

{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once.say
`,
    },
    {
        label: { ja: "junction", en: "Junction" },
        source: `// all and any lift comparison into many choices.

say:
    if all [1, 2, 3] < any [2, 3, 4]:
        1
    else:
        0
`,
    },
    {
        label: { ja: "型", en: "Types" },
        source: `// our and pub bindings appear in the Types pane.

our id x = x
pub answer = id 42
pub name = id "Yulang"
pub pair = (answer, name)

pair.say
`,
    },
    {
        label: { ja: "console", en: "Console" },
        source: `// println is a library effect handled by the host.

println "hello from Yulang"
say: 1 + 2
`,
    },
    {
        label: { ja: "effect", en: "Effects" },
        source: `// A handler removes one effect and leaves the rest.

act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] _) =
    catch action:
        console::read(), k -> run_console: k 42

say:run_console:ask()
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
const languageButtons = document.querySelectorAll<HTMLButtonElement>(
    "[data-language-choice]",
);
const themeButtons = document.querySelectorAll<HTMLButtonElement>(
    "[data-theme-choice]",
);
const themeMediaQuery =
    typeof window.matchMedia === "function"
        ? window.matchMedia("(prefers-color-scheme: dark)")
        : undefined;
const translatableNodes = document.querySelectorAll<HTMLElement>("[data-i18n]");
const translatableAriaNodes =
    document.querySelectorAll<HTMLElement>("[data-i18n-aria]");
const docLinkNodes =
    document.querySelectorAll<HTMLAnchorElement>("[data-doc-link]");

let pendingRenderColor = 0;
let activeExampleIndex = 0;
let activeLang = resolveInitialLang();
let activeTheme: ThemeChoice = resolveInitialTheme();
let latestRun: CompletedRun | undefined;
let runGeneration = 0;
let isRunning = false;
let nextWorkerRequestId = 0;
let colorizeFallbackReported = false;
const pendingWorkerRequests = new Map<number, PendingWorkerRequest>();
let runWorker: Worker | undefined = createRunWorker();

setupI18n();
setupTheme();
setupExampleButtons();
loadExample(0);

await init({ module_or_path: await wasmModuleReady });
logEmbeddedStdArtifacts();

renderColor();
void runSource().finally(scheduleStdCacheWarmup);

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
runButton.addEventListener("click", () => {
    void runSource();
});

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

function setupTheme(): void {
    themeButtons.forEach((button) => {
        const choice = button.dataset.themeChoice;
        if (!isThemeChoice(choice)) {
            return;
        }
        button.addEventListener("click", () => {
            setTheme(choice);
        });
    });
    applyTheme();
    if (themeMediaQuery) {
        const onChange = () => {
            if (activeTheme === "system") {
                applyTheme();
            }
        };
        if (typeof themeMediaQuery.addEventListener === "function") {
            themeMediaQuery.addEventListener("change", onChange);
        } else if (
            typeof (
                themeMediaQuery as MediaQueryList & {
                    addListener?: (handler: () => void) => void;
                }
            ).addListener === "function"
        ) {
            (
                themeMediaQuery as MediaQueryList & {
                    addListener: (handler: () => void) => void;
                }
            ).addListener(onChange);
        }
    }
}

function setTheme(choice: ThemeChoice): void {
    if (activeTheme === choice) {
        return;
    }
    activeTheme = choice;
    try {
        localStorage.setItem("yulang-playground-theme", choice);
    } catch (error) {
        console.warn("Yulang theme persistence failed", error);
    }
    applyTheme();
}

function applyTheme(): void {
    const resolved = resolveTheme(activeTheme);
    document.documentElement.dataset.theme = activeTheme;
    document.documentElement.dataset.resolvedTheme = resolved;
    themeButtons.forEach((button) => {
        const choice = button.dataset.themeChoice;
        const isActive = choice === activeTheme;
        button.classList.toggle("is-active", isActive);
        button.setAttribute("aria-pressed", String(isActive));
    });
}

function resolveTheme(choice: ThemeChoice): ResolvedTheme {
    if (choice === "system") {
        return themeMediaQuery?.matches ? "dark" : "light";
    }
    return choice;
}

function resolveInitialTheme(): ThemeChoice {
    const stored =
        typeof localStorage !== "undefined"
            ? localStorage.getItem("yulang-playground-theme")
            : null;
    return isThemeChoice(stored) ? stored : "system";
}

function isThemeChoice(value: unknown): value is ThemeChoice {
    return value === "system" || value === "light" || value === "dark";
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
    docLinkNodes.forEach((link) => {
        const key = link.dataset.docLink;
        if (isDocLinkKey(key)) {
            const docLink = docLinks[activeLang][key];
            link.href = docLink.href;
            link.textContent = docLink.text;
        }
    });
    updateRunButton();
    if (isRunning) {
        result.textContent = t("running");
        types.textContent = t("running");
    } else if (!latestRun) {
        renderNotRunYet();
    }
}

function setupExampleButtons(): void {
    examples.forEach((example, index) => {
        const button = document.createElement("button");
        button.type = "button";
        button.className = "example-button";
        button.textContent = example.label[activeLang];
        button.addEventListener("click", () => {
            loadExample(index);
            void runSource();
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

async function runSource(): Promise<void> {
    const shouldCancelCurrentRun = isRunning;
    const generation = ++runGeneration;
    if (shouldCancelCurrentRun) {
        resetRunWorker("Yulang run superseded");
    }
    const source = sourceInput.value;
    const lang = activeLang;
    renderColor();
    showRunLoading();
    await nextPaint();
    if (generation !== runGeneration) {
        return;
    }
    const response = await requestRunWithWorkerRetry(source, lang, generation);
    if (generation !== runGeneration) {
        return;
    }
    if (response.ok) {
        latestRun = { output: response.output, source };
    } else {
        logWorkerRunFailure(response);
        latestRun = { output: workerErrorOutput(response.message), source };
    }
    isRunning = false;
    updateRunButton();
    renderRunOutput();
}

function renderRunOutput(): void {
    if (isRunning) {
        return;
    }
    if (!latestRun) {
        return;
    }
    const { output, source } = latestRun;
    if (output.timings) {
        console.debug("Yulang run timings", output.timings);
    }
    result.classList.remove("is-loading");
    types.classList.remove("is-loading");
    result.removeAttribute("aria-busy");
    types.removeAttribute("aria-busy");
    result.classList.toggle("is-error", !output.ok);
    types.classList.toggle("is-error", !output.ok);
    if (output.ok) {
        result.textContent = formatRunOutput(output);
        types.textContent = formatTypes(output.types);
    } else {
        result.textContent = output.diagnostics
            .map((diagnostic) => formatDiagnostic(diagnostic, source))
            .join("\n");
        types.textContent = "";
    }
}

function showRunLoading(): void {
    isRunning = true;
    updateRunButton();
    result.classList.remove("is-error");
    types.classList.remove("is-error");
    result.classList.add("is-loading");
    types.classList.add("is-loading");
    result.setAttribute("aria-busy", "true");
    types.setAttribute("aria-busy", "true");
    result.textContent = t("running");
    types.textContent = t("running");
}

function renderNotRunYet(): void {
    result.classList.remove("is-error", "is-loading");
    types.classList.remove("is-error", "is-loading");
    result.removeAttribute("aria-busy");
    types.removeAttribute("aria-busy");
    result.textContent = t("notRunYet");
    types.textContent = "";
}

function updateRunButton(): void {
    runButton.textContent = isRunning ? t("running") : t("run");
    runButton.disabled = isRunning;
    runButton.classList.toggle("is-loading", isRunning);
    runButton.setAttribute("aria-busy", String(isRunning));
}

function scheduleStdCacheWarmup(): void {
    const warm = () => {
        void requestWarmStdCache()
            .then((response) => {
                if (response.ok) {
                    console.debug("Yulang std cache warmup", response.output);
                } else if (shouldRetryInFreshWorker(response.message)) {
                    console.warn(
                        "Yulang std cache warmup failed",
                        response.message,
                    );
                    resetRunWorker(
                        `Yulang worker warmup trapped: ${response.message}`,
                    );
                } else {
                    console.warn(
                        "Yulang std cache warmup failed",
                        response.message,
                    );
                }
            })
            .catch((error) => {
                console.warn("Yulang std cache warmup failed", error);
            });
    };
    if ("requestIdleCallback" in window) {
        window.requestIdleCallback(warm, { timeout: 1000 });
    } else {
        globalThis.setTimeout(warm, 0);
    }
}

function logEmbeddedStdArtifacts(): void {
    console.debug(
        "Yulang embedded std artifacts",
        embedded_std_compiled_unit_artifact_status() as EmbeddedStdArtifactsOutput,
    );
}

async function requestRunWithWorkerRetry(
    source: string,
    lang: Lang,
    generation: number,
): Promise<RunResponse> {
    const first = await requestRunOrError(source, lang, generation);
    if (first.ok) {
        return first;
    }
    if (!shouldRetryInFreshWorker(first.message)) {
        return first;
    }
    logWorkerRunFailure(first);
    resetRunWorker(`Yulang worker trapped: ${first.message}`);
    const retry = await requestRunOrError(source, lang, generation);
    return retry;
}

async function requestRunOrError(
    source: string,
    lang: Lang,
    generation: number,
): Promise<RunResponse> {
    try {
        return await requestRun(source, lang);
    } catch (error) {
        return {
            id: generation,
            kind: "run",
            ok: false,
            message: error instanceof Error ? error.message : String(error),
        };
    }
}

function requestRun(source: string, lang: Lang): Promise<RunResponse> {
    return requestWorker({
        id: nextWorkerRequestId++,
        kind: "run",
        source,
        lang,
    }) as Promise<RunResponse>;
}

function requestWarmStdCache(): Promise<WarmStdCacheResponse> {
    return requestWorker({
        id: nextWorkerRequestId++,
        kind: "warm-std-cache",
    }) as Promise<WarmStdCacheResponse>;
}

function requestWorker(request: RunWorkerRequest): Promise<RunWorkerResponse> {
    if (!runWorker) {
        runWorker = createRunWorker();
    }
    const worker = runWorker;
    return new Promise((resolve, reject) => {
        pendingWorkerRequests.set(request.id, { reject, resolve });
        try {
            worker.postMessage(request);
        } catch (error) {
            pendingWorkerRequests.delete(request.id);
            reject(error);
        }
    });
}

function rejectPendingWorkerRequests(reason: unknown): void {
    resetRunWorker(reason);
}

function resetRunWorker(reason: unknown): void {
    const error = reason instanceof Error ? reason : new Error(String(reason));
    runWorker?.terminate();
    runWorker = createRunWorker();
    for (const pending of pendingWorkerRequests.values()) {
        pending.reject(error);
    }
    pendingWorkerRequests.clear();
}

function createRunWorker(): Worker {
    const worker = new Worker(new URL("./run-worker.ts", import.meta.url), {
        type: "module",
    });
    void wasmModuleReady.then((module) => {
        worker.postMessage({ kind: "init-wasm", module });
    });
    worker.addEventListener(
        "message",
        (event: MessageEvent<RunWorkerResponse>) => {
            const pending = pendingWorkerRequests.get(event.data.id);
            if (!pending) {
                return;
            }
            pendingWorkerRequests.delete(event.data.id);
            pending.resolve(event.data);
        },
    );
    worker.addEventListener("error", (event) => {
        rejectPendingWorkerRequests(
            new Error(event.message || "Yulang worker failed"),
        );
    });
    worker.addEventListener("messageerror", () => {
        rejectPendingWorkerRequests(
            new Error("Yulang worker response is unreadable"),
        );
    });
    return worker;
}

function workerErrorOutput(message: string): RunOutput {
    return {
        ok: false,
        results: [],
        stdout: "",
        types: [],
        diagnostics: [
            {
                severity: "error",
                message,
                related: [],
            },
        ],
    };
}

function logWorkerRunFailure(response: RunWorkerErrorResponse<"run">): void {
    console.warn("Yulang worker run failed", {
        name: response.name,
        message: response.message,
        context: response.context,
        stack: response.stack,
    });
}

function shouldRetryInFreshWorker(message: string): boolean {
    return (
        message.includes("Maximum call stack size exceeded") ||
        message.includes("unreachable")
    );
}

function nextPaint(): Promise<void> {
    return new Promise((resolve) => {
        window.requestAnimationFrame(() => {
            window.setTimeout(resolve, 0);
        });
    });
}

function formatRunOutput(output: RunOutput): string {
    const parts: string[] = [];
    const stdout = output.stdout.endsWith("\n")
        ? output.stdout.slice(0, -1)
        : output.stdout;
    if (stdout.length > 0) {
        parts.push(stdout);
    }
    if (output.results.length > 0) {
        parts.push(formatResults(output.results));
    }
    if (parts.length === 0) {
        return t("noOutput");
    }
    return parts.join("\n");
}

function formatResults(results: RunResult[]): string {
    if (results.length === 0) {
        return t("noOutput");
    }
    if (results.length === 1) {
        return `${t("resultLine")}: ${results[0].value}`;
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
    editorHighlightContent.innerHTML = colorizedSourceHtml(sourceInput.value);
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
        const start = clampSourceOffset(span.start, source.length);
        const end = clampSourceOffset(span.end, source.length);
        if (start < cursor || end < start) {
            continue;
        }
        html += escapeHtml(source.slice(cursor, start));
        html += `<span class="tok tok-${span.kind}">${escapeHtml(
            source.slice(start, end),
        )}</span>`;
        cursor = end;
    }
    html += escapeHtml(source.slice(cursor));
    return preserveTrailingLine(source, html);
}

function colorizedSourceHtml(source: string): string {
    try {
        const output = colorize(source) as ColorizeOutput;
        const spans = Array.isArray(output.spans) ? output.spans : [];
        return highlightSource(source, spans);
    } catch (error) {
        reportColorizeFallback(error);
        return plainSourceHtml(source);
    }
}

function plainSourceHtml(source: string): string {
    return preserveTrailingLine(source, escapeHtml(source));
}

function preserveTrailingLine(source: string, html: string): string {
    if (source.endsWith("\n")) {
        return `${html} `;
    }
    return html;
}

function clampSourceOffset(offset: number, sourceLength: number): number {
    if (!Number.isFinite(offset)) {
        return 0;
    }
    return Math.max(0, Math.min(sourceLength, offset));
}

function reportColorizeFallback(error: unknown): void {
    if (colorizeFallbackReported) {
        return;
    }
    colorizeFallbackReported = true;
    console.warn("Yulang colorizer failed; rendering plain source", error);
}

function formatDiagnostic(diagnostic: Diagnostic, source: string): string {
    const code = diagnostic.code ? ` [${diagnostic.code}]` : "";
    const message = diagnostic.label
        ? `${diagnostic.label}: ${diagnostic.message}`
        : diagnostic.message;
    const range =
        typeof diagnostic.start === "number" &&
        typeof diagnostic.end === "number"
            ? `\n  ${formatSourceRange(diagnostic.start, diagnostic.end, source)}`
            : "";
    const hint = diagnostic.hint ? `\n  hint: ${diagnostic.hint}` : "";
    const related =
        diagnostic.related.length === 0
            ? ""
            : diagnostic.related
                  .map((item) => `\n  - ${formatRelatedDiagnostic(item, source)}`)
                  .join("");
    return `${diagnostic.severity}${code}: ${message}${range}${hint}${related}`;
}

function formatRelatedDiagnostic(
    related: DiagnosticRelated,
    source: string,
): string {
    const origin = related.origin
        ? `; ${formatRelatedOrigin(related.origin)}`
        : "";
    const range = formatSourceRange(related.start, related.end, source);
    return `${related.message} (${range}${origin})`;
}

function formatRelatedOrigin(origin: DiagnosticRelatedOrigin): string {
    switch (origin) {
        case "type_annotation":
            return "type annotation";
        case "expression":
            return "expression";
        case "impl_candidate":
            return "impl candidate";
    }
}

type SourcePosition = {
    line: number;
    column: number;
    index: number;
};

type SourceFrame = {
    lineText: string;
    lineNumber: number;
    /** Zero-based UTF-16 offsets into lineText, suitable for String#slice. */
    startColumn: number;
    endColumn: number;
    continuedLineCount: number;
};

function extractSourceFrame(
    source: string,
    start: number,
    end: number,
): SourceFrame {
    const startOffset = clampSourceByteOffset(start);
    const endOffset = Math.max(startOffset, clampSourceByteOffset(end));
    const startPosition = sourcePositionAtByteOffset(source, startOffset);
    const endPosition = sourcePositionAtByteOffset(source, endOffset);
    const lineStart = source.lastIndexOf("\n", startPosition.index - 1) + 1;
    const nextLineBreak = source.indexOf("\n", startPosition.index);
    let lineEnd = nextLineBreak === -1 ? source.length : nextLineBreak;
    if (lineEnd > lineStart && source.charCodeAt(lineEnd - 1) === 0x0d) {
        lineEnd -= 1;
    }

    const lineText = source.slice(lineStart, lineEnd);
    const startColumn = Math.min(
        Math.max(0, startPosition.index - lineStart),
        lineText.length,
    );
    const endColumn =
        startPosition.line === endPosition.line
            ? Math.min(
                  Math.max(startColumn, endPosition.index - lineStart),
                  lineText.length,
              )
            : lineText.length;

    return {
        lineText,
        lineNumber: startPosition.line,
        startColumn,
        endColumn,
        continuedLineCount: Math.max(
            0,
            endPosition.line - startPosition.line,
        ),
    };
}

function formatSourceRange(start: number, end: number, source: string): string {
    const startPosition = sourcePositionAtByteOffset(source, start);
    const endPosition = sourcePositionAtByteOffset(source, end);
    if (
        startPosition.line === endPosition.line &&
        startPosition.column === endPosition.column
    ) {
        return `line ${startPosition.line}:${startPosition.column}`;
    }
    if (startPosition.line === endPosition.line) {
        return `line ${startPosition.line}:${startPosition.column}-${endPosition.column}`;
    }
    return `line ${startPosition.line}:${startPosition.column}-line ${endPosition.line}:${endPosition.column}`;
}

function sourcePositionAtByteOffset(
    source: string,
    targetOffset: number,
): SourcePosition {
    const clampedTargetOffset = clampSourceByteOffset(targetOffset);
    let byteOffset = 0;
    let line = 1;
    let column = 1;
    let index = 0;
    while (index < source.length) {
        const codePoint = source.codePointAt(index);
        if (codePoint === undefined) {
            break;
        }
        const byteLength = utf8ByteLengthOfCodePoint(codePoint);
        if (byteOffset + byteLength > clampedTargetOffset) {
            break;
        }
        byteOffset += byteLength;
        index += codePoint > 0xffff ? 2 : 1;
        if (codePoint === 0x0a) {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    return { line, column, index };
}

function clampSourceByteOffset(offset: number): number {
    if (!Number.isFinite(offset)) {
        return 0;
    }
    return Math.max(0, offset);
}

function utf8ByteLengthOfCodePoint(codePoint: number): number {
    if (codePoint <= 0x7f) {
        return 1;
    }
    if (codePoint <= 0x7ff) {
        return 2;
    }
    if (codePoint <= 0xffff) {
        return 3;
    }
    return 4;
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

function isDocLinkKey(key: string | undefined): key is DocLinkKey {
    return key !== undefined && key in docLinks.en;
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

function redirectCleanDocsPath(): void {
    const pathname = window.location.pathname;
    if (pathname.endsWith("/") || pathname.endsWith(".html")) {
        return;
    }

    let target: string | undefined;
    if (isDocsIndexCleanPath(pathname)) {
        target = `${pathname}/`;
    } else if (isDocsArticleCleanPath(pathname)) {
        target = `${pathname}.html`;
    }

    if (target === undefined) {
        return;
    }
    window.location.replace(
        `${target}${window.location.search}${window.location.hash}`,
    );
}

function isDocsIndexCleanPath(pathname: string): boolean {
    return /^\/(?:ja\/)?(?:guide|reference)$/.test(pathname);
}

function isDocsArticleCleanPath(pathname: string): boolean {
    if (!/^\/(?:ja\/)?(?:guide|reference)\/.+/.test(pathname)) {
        return false;
    }
    const basename = pathname.slice(pathname.lastIndexOf("/") + 1);
    return !basename.includes(".");
}
