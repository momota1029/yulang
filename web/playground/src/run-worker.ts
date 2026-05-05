import init, { run } from "./wasm/yulang_wasm.js";

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

type RunWorkerRequest = {
  id: number;
  source: string;
};

type RunWorkerResponse = {
  id: number;
  output: RunOutput;
};

const wasmReady = init();

self.addEventListener("message", (event: MessageEvent<RunWorkerRequest>) => {
  void runSource(event.data);
});

async function runSource(request: RunWorkerRequest): Promise<void> {
  const output = await runSourceOutput(request.source);
  const response: RunWorkerResponse = {
    id: request.id,
    output,
  };
  self.postMessage(response);
}

async function runSourceOutput(source: string): Promise<RunOutput> {
  try {
    await wasmReady;
    return run(source) as RunOutput;
  } catch (error) {
    return runtimeErrorOutput(errorMessage(error), source.length);
  }
}

function runtimeErrorOutput(message: string, sourceLength: number): RunOutput {
  return {
    ok: false,
    results: [],
    types: [],
    diagnostics: [
      {
        severity: "error",
        message,
        start: sourceLength,
        end: sourceLength,
      },
    ],
  };
}

function errorMessage(error: unknown): string {
  if (error instanceof Error) {
    return error.message;
  }
  return String(error);
}
