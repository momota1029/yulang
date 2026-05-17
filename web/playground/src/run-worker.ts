/// <reference lib="webworker" />

import init, {
  clear_std_cache,
  run,
  warm_std_cache,
} from "./wasm/yulang_wasm.js";

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

type WorkerControlMessage = {
  kind: "init-wasm";
  module: WebAssembly.Module;
};

type RunWorkerResponse =
  | {
      id: number;
      kind: "run";
      ok: true;
      output: unknown;
    }
  | {
      id: number;
      kind: "warm-std-cache";
      ok: true;
      output: unknown;
    }
  | {
      id: number;
      kind: RunWorkerRequest["kind"];
      ok: false;
      message: string;
      name?: string;
      stack?: string;
      context: WorkerDebugContext;
    };

const workerSelf = self as DedicatedWorkerGlobalScope;
const workerStartedAt = Date.now();
let handledRequests = 0;
let lastStarted: WorkerRequestTrace | undefined;
let lastCompleted: WorkerRequestTrace | undefined;
let lastRunUsedContinuations = false;
let lastRunClearedCache = false;
let resolveWasmReady: (value: unknown) => void;
let rejectWasmReady: (reason?: unknown) => void;
const wasmReady = new Promise<unknown>((resolve, reject) => {
  resolveWasmReady = resolve;
  rejectWasmReady = reject;
});

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

workerSelf.addEventListener(
  "message",
  (event: MessageEvent<RunWorkerRequest | WorkerControlMessage>) => {
    const data = event.data;
    if (
      typeof data === "object" &&
      data !== null &&
      "kind" in data &&
      data.kind === "init-wasm"
    ) {
      try {
        const ready = init({ module_or_path: data.module });
        ready.then(resolveWasmReady, rejectWasmReady);
      } catch (error) {
        rejectWasmReady(error);
      }
      return;
    }
    void handleRequest(data as RunWorkerRequest);
  },
);

async function handleRequest(request: RunWorkerRequest): Promise<void> {
  const trace: WorkerRequestTrace = {
    id: request.id,
    kind: request.kind,
    started_ms: Date.now() - workerStartedAt,
    source_chars: request.kind === "run" ? request.source.length : undefined,
  };
  lastStarted = trace;
  handledRequests += 1;
  try {
    await wasmReady;
    if (request.kind === "run") {
      const output = run(request.source);
      const continuationSteps = continuationStepsOf(output);
      trace.continuation_steps = continuationSteps;
      trace.cache_cleared = continuationSteps > 0;
      lastRunUsedContinuations = continuationSteps > 0;
      lastRunClearedCache = continuationSteps > 0;
      if (continuationSteps > 0) {
        clear_std_cache();
      }
      markCompleted(trace, true);
      postResponse({
        id: request.id,
        kind: request.kind,
        ok: true,
        output,
      });
      return;
    }
    const output = warm_std_cache();
    markCompleted(trace, true);
    postResponse({
      id: request.id,
      kind: request.kind,
      ok: true,
      output,
    });
  } catch (error) {
    const details = errorDetails(error);
    markCompleted(trace, false);
    console.warn("Yulang worker request failed", {
      trace,
      context: debugContext(),
      error: details,
    });
    postResponse({
      id: request.id,
      kind: request.kind,
      ok: false,
      message: details.message,
      name: details.name,
      stack: details.stack,
      context: debugContext(),
    });
  }
}

function markCompleted(trace: WorkerRequestTrace, ok: boolean): void {
  trace.finished_ms = Date.now() - workerStartedAt;
  trace.ok = ok;
  lastCompleted = { ...trace };
}

function debugContext(): WorkerDebugContext {
  return {
    worker_age_ms: Date.now() - workerStartedAt,
    handled_requests: handledRequests,
    last_started: lastStarted,
    last_completed: lastCompleted,
    last_run_used_continuations: lastRunUsedContinuations,
    last_run_cleared_cache: lastRunClearedCache,
  };
}

function continuationStepsOf(output: unknown): number {
  if (
    typeof output !== "object" ||
    output === null ||
    !("timings" in output) ||
    typeof output.timings !== "object" ||
    output.timings === null ||
    !("vm_continuation_steps" in output.timings) ||
    typeof output.timings.vm_continuation_steps !== "number"
  ) {
    return 0;
  }
  return output.timings.vm_continuation_steps;
}

function postResponse(response: RunWorkerResponse): void {
  workerSelf.postMessage(response);
}

function errorDetails(error: unknown): {
  message: string;
  name?: string;
  stack?: string;
} {
  if (error instanceof Error) {
    return {
      message: error.message,
      name: error.name,
      stack: error.stack,
    };
  }
  return {
    message: String(error),
  };
}
