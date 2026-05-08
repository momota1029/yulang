/// <reference lib="webworker" />

import init, {
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
    };

const workerSelf = self as DedicatedWorkerGlobalScope;
const wasmReady = init();

workerSelf.addEventListener("message", (event: MessageEvent<RunWorkerRequest>) => {
  void handleRequest(event.data);
});

async function handleRequest(request: RunWorkerRequest): Promise<void> {
  try {
    await wasmReady;
    if (request.kind === "run") {
      postResponse({
        id: request.id,
        kind: request.kind,
        ok: true,
        output: run(request.source),
      });
      return;
    }
    postResponse({
      id: request.id,
      kind: request.kind,
      ok: true,
      output: warm_std_cache(),
    });
  } catch (error) {
    const details = errorDetails(error);
    postResponse({
      id: request.id,
      kind: request.kind,
      ok: false,
      message: details.message,
      name: details.name,
      stack: details.stack,
    });
  }
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
