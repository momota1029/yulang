# R84 Lean slot 1 result — normalized dependency prefix

Authorization: `tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-slot1-authorization.md`, committed and pushed at `5c0414016` before invocation.

- Exact stdin: 93,368 bytes; SHA-256 `e031132b1a5a42f22c5faba355a1af3d8639d0d577de9051e81f403bf465ebb3`.
- Pinned Lean executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`; SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Invocation: `lean -j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; 120-second timeout.
- Exit: **0**. Timeout: **no**. Elapsed: **9.034 seconds**. Child peak RSS: **862,772 KiB**.
- Stdout observed: 82,453 bytes; SHA-256 `8d605c1e2ae9b534cf25607dc314512b617a08bf0ecf07463730590bd720e4a9`.
- Stderr: 0 bytes; SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## Stream-retention incident

The audit runner captured stdout in memory and encoded it into the command
response instead of writing the completed stream directly into this primary
result record. The tool response truncated that large encoded output. The
complete stdout bytes therefore were **not retained**, although their byte
count and SHA-256 were observed before the response truncation. The process
itself exited 0; this was not a Lean error or timeout. No identical invocation
is authorized by the R84 stage plan.

Consequently, record this as **prefix process exit 0; receipt retention
incomplete**. Do not claim independent review of the emitted prefix types or
axiom reports, do not promote any theorem, and do not authorize slot 3 from this
receipt alone. Preserve the exact input and execution metadata above; resolve
the receipt-integrity gate through an explicit versioned decision before any
further checker invocation.
