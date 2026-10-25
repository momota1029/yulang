# R59 primary verification receipt — stopped on capture gap

Sprint: `PAPER-HEAP-OBSERVATION-20261026/r59`
Baseline: `4eb348f7ebf53509ae701c6b0434041a90f8f573`
Branch: `yulang3`
Disposition: **PRIMARY VERIFICATION NOT ESTABLISHED; STOPPED**. This is a process-evidence failure, not a mathematical counterexample. No root import or integration is authorized by this receipt.

## Frozen intake

Source handoff SHA-256: `b7976c6ae7a8a276b4a59e479b71bc0bdec20696a974dff367492e02541ac5f6`.
Proof handoff SHA-256: `a115016535753182240188232262e8f19613fbf6e8784137048bd5f632e8f9bf`.
Worker check log SHA-256: `b3847d011403975667bf2cbddb897c0934bf71912627d9200c035e51f946982a`.
Candidate SHA-256 (worker isolated checkout): `19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f`.
Audit source SHA-256 (worker isolated checkout): `07327b553d9f51e1e5dcfc2e352cc72953c6e7bb943d819777ce4d9967f98aed`.
Worker's 96-file build-cache manifest SHA-256: `b79a2fc5ed4abb0173b02df86286615cb09a6c15d7020aaa52aefa53f5977dab`. The primary did not use this cache.

I created a separate detached primary worktree at the exact baseline and copied only the frozen candidate and audit source into it. All 18 hashes in the R59 contract's frozen-input block matched. The primary worktree HEAD was the exact baseline. Native Lake resolved read-only to `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`.

## Primary checker calls

Calls 1 and 2 completed with captured output:

1. argv `[/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake, --version]`; cwd `/tmp/yulang-r59-primary/notes/theory/lean`; exit 0. stdout (53 bytes), SHA-256 `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`:
   ```text
   Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
   ```
   stderr empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
2. argv `[/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake, env, lean, --version]`; same cwd; exit 0. stdout (106 bytes), SHA-256 `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`:
   ```text
   Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
   ```
   stderr empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Call 3 launched the required focused build with `LEAN_NUM_THREADS=1`:

```text
argv: [/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake, build, +YulangClosure.PaperHeapObservation]
cwd: /tmp/yulang-r59-primary/notes/theory/lean
timeout supplied to subprocess: 180 seconds
```

The command ran through an `exec_command` session inside an orchestration wrapper. I printed only its output field and discarded the returned session identifier. The initial response had no captured output; a subsequent process inspection found no remaining Lean/Lake process. Therefore this receipt cannot recover the command's exit status, complete stdout/stderr, or exact duration. Those values are **UNKNOWN**; no success is inferred from the worker's independent build. The build call may have completed, but its primary evidence is lost.

Per the R59 contract, the first failed/incomplete primary-verification capture stops the sprint. I did not retry the command or run call 4 (the complete audit). Primary checker count is 3 of 4; checker seconds for call 3 are UNKNOWN. Conservatively charging its supplied 180-second process timeout exceeds the 90-second primary checker cap, so the cap cannot be certified. No fresh review was started. The independent review and root-import gates remain closed.

## Bounded proof and source result (worker evidence only)

The worker reports a passing focused build and complete 37-declaration audit on its frozen candidate, with only `propext` and `Quot.sound`; this is retained as worker evidence, not substituted for primary verification. Its bounded theorem path covers finite graph read/type-beta observations, the exact R29 allocation result, Force/Delay, and an explicit self-alias loop. Guardedness, termination, source/native realization, full executor preservation, inference A/B, and production remain OPEN.

The source lane's independent static trace falsifies direct identification of Rust's mutable `None → Some` cells with R29's immutable heap and reports `NO_SAFE_CODE_SLICE`. It does not refute a future published-cell simulation relation. Source realization remains OPEN.

No external proof artifact arrived during this sprint. Questions remain withdrawn. All original parent gates remain OPEN.

## Cessation and next gate

Both writers stopped; their frozen hashes and receipts are preserved. The primary checker process is no longer running. No root import or Lean integration was performed. The candidate remains only in the isolated worktrees and is not accepted into the public root.

A later, separately authorized verification packet must define a fresh capture path that retains session IDs and complete raw process output before any primary check begins. This receipt does not authorize a retry inside R59.
