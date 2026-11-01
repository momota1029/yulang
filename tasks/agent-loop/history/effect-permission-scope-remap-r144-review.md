# R144 independent Rust source review

Reviewer: `/root/r144_scope_review`, fresh compiler referee, distinct from implementation and source/proof mapper. Read-only inspection; no source writes or execution. Review was based on the exact frozen input hashes below and baseline `77cf25096f8271590b89380fc988d7e2dd11e7d6`.

Verdict: **REJECT frozen candidate pending correction**. The change adds validation coverage only and repairs no production behavior. Oracle independence and caller-map limitations are sound by inspection. Source remains UNCOMPILED / UNEXECUTED.

## Blocking finding

`crates/yu-solver/src/candidate_scope.rs:499–508` creates `stamp(a).then(protect(x,a)).then(protect(y,b))`, then expects `scope_map` calls for both `x` and `y`. In `then` at lines 160–169, the earlier stamp removes `a` from the second guard, so the `x` entry becomes identity and is omitted. Final support contains only `y`; remap calls `scope_map(y)` once, so the assertion necessarily fails. The fixture also does not test deduplication of an input occurring in both stamp and retained-guard support.

Minimum correction: retain `protect(x,a)` before `stamp(a)`, followed by `protect(y,b)`. This retains both scope entries and makes `a` occur in both retained guard and stamp support; keep independent expected closure counts.

## Minor findings

1. `candidate_scope.rs:453–470`: the remap/evaluate commutation fixture supplies both input IDs initially and already protects `x`. Its `x` guard is false, and a broken input-ID rename can remain invisible because `x` is inherited. Add cases without inherited `x`: test `a` present and absent to distinguish guard suppression/addition after renaming.
2. `candidate_scope.rs:340–343,391–397`: exhaustive composition coverage folds primitive right operands only. It does not exercise a nonprimitive second transformer with multiple missing tags. Split bounded operation sequences at every boundary, compose both sides, and compare composed evaluation to successive production evaluations and the independent oracle.

## Other checks

- Oracle at lines 292–320 uses primitive `BTreeSet` insertion, membership and removal; it does not copy the `Missing` representation, canonical merge or production evaluator.
- Bounds are modest and deterministic: 585 sequences × 16 initial states = 9,360 comparisons.
- The four requested order distinctions, release tombstones, unsorted/duplicate slices, independent inherited protections and separate scope/input collision rejection are actually asserted.
- Rust privacy, ID ordering, equality, error comparisons, closure mutation and `#[cfg(test)]` placement appear plausible by inspection. Compilation is unverified.
- The 232-line diff adds one test module; production definitions do not change.
- Caller inspection confirms argument stamping, result protection, argument-scope release and lower-then-upper replay composition. The clean files contain no direct `ScopeTransformer.remap` invocation.
- The source/proof map honestly leaves authenticated external remap construction, shared incoming-state support, source/native correspondence, allocation failure, H, A/B and parent obligations OPEN. Its old-domain injection argument is conditional rather than authenticated caller evidence.
- No production phase, AST/CST, restoration, recovery or capture-grant behavior changes.

## Frozen identities

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_scope.rs` | `79b14e9e70bd4e906c223ffff4b2099c6bff843d89a8cd5cf7e02a63632cc2df` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-source.md` | `112a97edde389b2d4616cb0111b54971d10137073c7d9dc7c546f306cea98ee0` |
| `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-proof.md` | `dfcd7412c4d2592327e4b4c2e2e481531d008026d77fd5d2636d50da9b4e4581` |

No Rust/Cargo/Lean/build/test/scratch execution or filesystem writes occurred during review. Implementer explanation was read only after independent source inspection and did not count as correctness evidence.

Reviewer state: **STOPPED**; no descendants, writes or pending processes. Luna owns repair/adjudication.

## Delta review after primary repair

Primary repaired only the test module after the above REJECT verdict. No worker wrote source while the first review was active; the initial rejected candidate remains described by its original hash above. The exact repaired source is now SHA-256 `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.

Delta verdict: **ACCEPT as an UNCOMPILED / UNEXECUTED regression candidate**. All three prior findings are closed by source inspection:

- The closure fixture protects `x` before stamping `a`; both `x` and `y` survive, and `a` appears in retained guard and stamped support. Exactly-once expectations match distinct support.
- The remap test checks absent and present `a` with no inherited protections; a guard-renaming failure changes observable output.
- Every bounded sequence is split at every boundary. Each split compares evaluation of `first.then(second)` against direct successive production evaluation, including nonprimitive right transformers. The independent primitive oracle comparison remains.

Bounds remain fixed: 585 sequences × 16 states, at most four split checks per case. The production prefix (lines 1–279) still hashes to admitted baseline SHA-256 `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`; no production definition changed. No additional delta finding. Caller-map limitations and parent OPEN gates are unchanged.

The reviewer performed only short read/hash operations, completed within the additional 60-second continuation of the original review budget, and did not compile, build, run tests, run Lean, create scratch, touch Git or write files. **STOPPED**, no descendants or pending processes.
