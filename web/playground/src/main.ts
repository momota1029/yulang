import init, {
    colorize,
    embedded_std_compiled_unit_artifact_status,
} from "./wasm/yulang_wasm.js";
import wasmUrl from "./wasm/yulang_wasm_bg.wasm?url";
import "./style.css";

const wasmModuleReady: Promise<WebAssembly.Module> = WebAssembly.compileStreaming(
    fetch(wasmUrl),
);

type Diagnostic = {
    severity: "error";
    message: string;
    start: number;
    end: number;
};

type RunOutput = {
    ok: boolean;
    results: RunResult[];
    stdout: string;
    types: TypeResult[];
    timings?: RunTimings;
    diagnostics: Diagnostic[];
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
    cache_cleared?: boolean;
};

type WorkerDebugContext = {
    worker_age_ms: number;
    handled_requests: number;
    last_started?: WorkerRequestTrace;
    last_completed?: WorkerRequestTrace;
    last_run_used_continuations: boolean;
    last_run_cleared_cache: boolean;
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

type DocLinkKey = "guide" | "reference";

const messages: Record<Lang, Record<MessageKey, string>> = {
    ja: {
        run: "実行",
        running: "実行中",
        result: "結果",
        types: "型",
        typesAria: "型推論",
        examples: "例",
        noOutput: "(出力なし)",
        noExportedTypes: "(公開された型なし)",
        notRunYet: "実行すると結果がここに表示されます。",
        resultLine: "結果",
        themeSystem: "自動",
        themeLight: "ライト",
        themeDark: "ダーク",
    },
    en: {
        run: "Run",
        running: "Running",
        result: "Result",
        types: "Types",
        typesAria: "Type inference",
        examples: "Examples",
        noOutput: "(no output)",
        noExportedTypes: "(no exported types)",
        notRunYet: "Run the program to show results here.",
        resultLine: "Result",
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
    },
    en: {
        guide: { href: "/guide/", text: "Guide" },
        reference: { href: "/reference/", text: "Reference" },
    },
};

const examples: Example[] = [
    {
        label: { ja: "ツアー", en: "Tour" },
        source: `// === A compact tour of Yulang ===

// methods sit next to the type they extend
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2

// nondeterministic search: every Pythagorean triple under 15
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list

// junction lifts a comparison over many choices at once
if all [1, 2, 3] < any [3, 4, 5]:
    "every left dominated"
else:
    "no"

// symbol variants: ad-hoc tagged choices, matched right inline
my render option = case option:
    :ok msg -> "[ok] " + msg
    :err code -> "[err " + code.show + "]"
    :pending -> "..."

[render(:ok "hello"), render(:err 404), render :pending]

// a user-defined effect: \`coin\` calls the continuation TWICE,
// so one run explores every branch.
act flip:
    our coin: () -> bool

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
`,
    },
    {
        label: { ja: "データとメソッド", en: "Data & Methods" },
        source: `// Struct methods live next to the data they extend.

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
`,
    },
    {
        label: { ja: "名前付き既定値", en: "Named Defaults" },
        source: `// Record patterns make named options lightweight.

my box {width = 1, height = width} =
    width * height

box {}
box { width: 3 }
box { width: 3, height: 4 }
`,
    },
    {
        label: { ja: "ボタン", en: "Button" },
        source: `// Symbol variants are lightweight choices with payloads.

my button option = case option:
    :label text -> "<button>%{text}</button>"
    :disabled -> "<button disabled></button>"

button: :label "send"
button: :disabled
`,
    },
    {
        label: { ja: "局所的な変更", en: "Local Change" },
        source: `// A mutable binding stays local to the surrounding block.

my $total = 0
for x in 1..5:
    &total = $total + x
$total
`,
    },
    {
        label: { ja: "リスト更新", en: "List Update" },
        source: `// Child references make nested updates direct.

my $xs = [
    2
    3
    4
]
&xs[1] = 6
$xs
`,
    },
    {
        label: { ja: "sub return", en: "Sub Return" },
        source: `// sub gives an expression a local return.

my first_over limit = sub:
    for x in 0..: if x * x > limit: return x
    0

first_over 40
`,
    },
    {
        label: { ja: "callback 衛生性", en: "Callback Hygiene" },
        source: `// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \\i -> if i == 0: return i
    println b.show
    2
`,
    },
    {
        label: { ja: "非決定 list", en: "Nondet List" },
        source: `// each branches; .list collects every result.

(each [1, 2, 3] + each [4, 5, 6]).list
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
} .once
`,
    },
    {
        label: { ja: "junction", en: "Junction" },
        source: `// all and any lift comparison into many choices.

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

pair
`,
    },
    {
        label: { ja: "console", en: "Console" },
        source: `// println is a library effect handled by the host.

println "hello from Yulang"
1 + 2
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
let latestRunOutput: RunOutput | undefined;
let runGeneration = 0;
let isRunning = false;
let nextWorkerRequestId = 0;
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
    } else if (!latestRunOutput) {
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
    const generation = ++runGeneration;
    const source = sourceInput.value;
    renderColor();
    showRunLoading();
    await nextPaint();
    if (generation !== runGeneration) {
        return;
    }
    const response = await requestRunWithWorkerRetry(source, generation);
    if (generation !== runGeneration) {
        return;
    }
    if (response.ok) {
        latestRunOutput = response.output;
    } else {
        logWorkerRunFailure(response);
        latestRunOutput = workerErrorOutput(response.message);
    }
    isRunning = false;
    updateRunButton();
    renderRunOutput();
}

function renderRunOutput(): void {
    if (isRunning) {
        return;
    }
    if (!latestRunOutput) {
        return;
    }
    const output = latestRunOutput;
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
            .map(formatDiagnostic)
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
    generation: number,
): Promise<RunResponse> {
    const first = await requestRunOrError(source, generation);
    if (first.ok) {
        resetWorkerAfterContinuationRun(first.output);
        return first;
    }
    if (!shouldRetryInFreshWorker(first.message)) {
        return first;
    }
    logWorkerRunFailure(first);
    resetRunWorker(`Yulang worker trapped: ${first.message}`);
    const retry = await requestRunOrError(source, generation);
    if (retry.ok) {
        resetWorkerAfterContinuationRun(retry.output);
    }
    return retry;
}

async function requestRunOrError(
    source: string,
    generation: number,
): Promise<RunResponse> {
    try {
        return await requestRun(source);
    } catch (error) {
        return {
            id: generation,
            kind: "run",
            ok: false,
            message: error instanceof Error ? error.message : String(error),
        };
    }
}

function requestRun(source: string): Promise<RunResponse> {
    return requestWorker({
        id: nextWorkerRequestId++,
        kind: "run",
        source,
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
                start: 0,
                end: 0,
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

function resetWorkerAfterContinuationRun(output: RunOutput): void {
    if ((output.timings?.vm_continuation_steps ?? 0) === 0) {
        return;
    }
    resetRunWorker("Yulang worker recycled after continuation-heavy run");
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
