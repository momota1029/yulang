# R149 in-crate capture — outcome

Sprint: `R149-IN-CRATE-CAPTURE-20261024`, contract revision 2, SHA-256
`7718897585334c1baae5b274d6f12c7ded9587fdb7a64c3b8fe179b4aa69effa`.
Baseline: `424566114b10aaa948c2a0ffac53f56567416114`.
Worktree: `/tmp/yulang-r149-in-crate-capture-20261024`, branch
`codex/r149-in-crate-capture-20261024`.

## Result

**PARTIAL_REVIEWED; the sole build failed in the temporary readback example, so
there is no parser or HIR observation.** The reviewed delta reached the
authorized driver-build step, but compilation stopped before any source parse,
provider-index readback, or runtime observation. R149, source-to-CST/HIR, the
original A/B claims, and the full inference/evaluator goal remain OPEN. No
compiler defect or theorem closure is claimed.

The two compiler errors are both in the temporary example's generic `debug`
helper: its implicit `Sized` bound rejects `[SyntaxDependencyProvenance]` at
line 185 and `[HirError]` at line 321. The recorded minimal repair is
`T: Debug + ?Sized`. This is not an observed parser/HIR failure. The repair and
another build were not authorized under revision 2.

## Frozen evidence and review

- Worktree code: `tools/inference-playground/src/lib.rs`, SHA-256
  `91ee545c8b9255174ea283409ea2ad30f5878f3b4c7129b96a77d22999a9c5fd`.
- Temporary example:
  `tools/inference-playground/examples/r149_exact_source_readback.rs`, SHA-256
  `2313bf7d8447012bc29853215cade2a6c69a3240355f55577e6e6b285ea29f9e`.
- Both embedded source templates matched their pinned bytes: Types (142 bytes,
  SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`)
  and Console (92 bytes, SHA-256
  `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`).
- Fresh independent code-delta review: **PASS** after the initial review's JSON
  and key-join findings were repaired. The final review confirmed valid JSON,
  actual key equality and matched CST identity facts, error provenance, the
  authorized constructor order, and the stop before `pinned_candidate_world`.
- Sole command: `target/r149-in-crate-capture-20261024/command.txt`, SHA-256
  `5324004b223d7d9949ef4bcc9467c12bce2dd8a61b22e3af3a067a971878d05d`.
  Elapsed 42.73 seconds; exit code 101; stderr SHA-256
  `3d73216fd3020beed3b53ff7ad8fd685c875a0720ada9cb131f30d452cfe2f45d`.
  Stdout and `readback.json` were both empty (SHA-256
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
- Proof/source handoff in the isolated worktree:
  `notes/theory/2026-10-24-r149-in-crate-capture.md`, SHA-256
  `f35a59d6bf9f8ae4eec5833ce04329eaa47031c649fed98775b1aa8c1fe06afa`;
  inbox `tasks/agent-loop/inbox/20261024-r149-in-crate-capture.md`, SHA-256
  `f9e32b6d9343bae7781fa2833e48bf262680b4e3939a110f09ea6a675f245b97`.
  The note contains only a conditional source-prefix argument and explicitly
  records **NO OBSERVATION / NO ACTUAL IDENTITY JOIN**.

## Scope and next step

No second build, tests, evaluator/runtime execution, parser process, or sample
readback occurred. The temporary source/example delta remains isolated and
unintegrated. Three legacy worker reservations remain UNKNOWN and quarantined.

The proof note is a useful parallel-work location for this packet. Any future
code repair and build require a new exact authorization, fresh review, and a
new sprint resource allocation; revision 2 grants none. Do not merge or copy
the isolated source/proof artifacts into the main worktree until the UNKNOWN
reservations have confirmed cessation or lease handoff.
