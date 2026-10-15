# Playground raw continuation execution

Date: 2026-10-16
Branch: research/simple-sub-intrusion
Baseline: receiving implementation 46bb232a4; native-only HEAD 419c801bd
Status: cache-free captured-context implementation and its actual control proof
complete; original full-domain Resume and whole-language parents OPEN.

## Scope and authority

Existing charter §§13–17, source scheduling and typed-source owner rules govern
raw resumption: whole response arguments are delayed, then enter as Value once;
contexts are reusable and use current shared cells. No store/activation snapshot
or one-use restriction is introduced. The selected shallow handler is excluded;
crossed forwarding handlers are reinstalled under their resolved owners.

The [constructor proof](../theory/2026-10-16-runtime-resume-template-correspondence.md)
first characterized every actual capture-frame constructor. Its independently
reviewed conditional derivation was consumed by implementation, then a fresh
review checked the actual constructors and consumers rather than promoting the
conditional theorem to an implementation fact.

## Actual construction

An immutable template contains Hole, Bind, Owner, ForwardHandler and View nodes,
including the containing owner when its ordinary return lies outside capture.
Invocation records retain original call/provider descriptors. A separate current
executable owner permits borrowing an original live owner below the resumer;
expired owners receive fresh executable occurrences without reviving their
receiving boundaries or rebinding historical evidence.

Owned and borrowed completions differ. Only owned completion retires an
activation; nested completion continues the captured suffix, while one capture
root returns to the resumer. View reentry allocates a fresh execution occurrence
with the original view/receipt. Recapture records currently resolved scopes,
not historical pop actions. Continuation arguments are forced once at actual
Value entry and checked against the original primitive response declaration.

The original checkpoint excluded multi-shot cache writes and guarded capture
containing GlobalRead/Root with ContinuationMaterialization. The subsequent
[delimiter corollary](../theory/2026-10-16-initialization-outward-order-current-runtime.md)
§8 closes that exact current-public-runtime pending-publication capture gate by
all-path unreachability after the approved initializer boundary repair. Its
fresh parent application review by `runtime_semantic_review` is CLEAN and the
primary accepts the bounded closure. The guard remains defensive; no A/B law or
source-domain restriction is selected. Captured cache references/current cells
remain supported, distinct from pending publication frames.

## Review and resource repair

M3 reviewers: `runtime_semantic_review`, `runtime_contract_review`, and
`receiving_cost`. An architect selected the resource repair under the existing
arena architecture; no additional language decision was needed.

The sole accepted major was recursive template ownership: a captured pending
ResumeArgument held an Arc to an older template, permitting deep recursive final
destruction. Templates now have one machine-owned flat arena and Copy handles in
every executable, frame and entry state. Capture validates before publication;
flat destruction never follows a template reference recursively.

The same batched repair replaced parent-chain owner lookup with a fresh moved
map per entry, and activity scans with invocation-owned bits. Constructive
inductions establish nearest-binding lookup equivalence and exact live-stack
membership. Error paths terminate the attempt without publishing a partial
template. Final code, actual proof, contract and resource deltas are clean.

Capture uses O(F+P) work/storage in one fuel transition; entry uses expected
O(F+P) total work and O(K) temporary owner-map space. P accounts for actual
payload/source/descriptor clone and hashing costs. Map destruction at Hole may
cost O(K), bounded by already-entered owner nodes. Retained template storage and
flat destruction are O(sum of captured nodes). The previous Grant-query bound
is restored by constant-time indexed activity. Fuel bounds transitions, not
absolute CPU work or allocation. Zero timing/RSS measurements ran.

## Verification and records

- First `CARGO_BUILD_JOBS=2 timeout 300s cargo test -p yu-playground --test
  runtime_resume -- --test-threads=2`: nine controls passed, no warnings.
- Final `CARGO_BUILD_JOBS=2 timeout 300s cargo test -p yu-playground --
  --test-threads=2`: 82 tests passed on the raw-Resume freeze, no failures/warnings.
  Includes nine resumption controls and one bounded 1,024-template handle/drop
  structural control. Later unintegrated primitive-classifier files are excluded
  from this verification claim.
- README stdin `k 11` example: candidate inference and `--run main -` exited 0,
  printing exactly `11`. Narrow documentation review is clean.
- Touched-file formatting and `git diff --check` passed. The sole existing test
  expectation/name update received pre-write approval: binding but not calling
  `k` returns the unchanged source's payload `7`.

Primary serialized Cargo, two jobs, two test threads. Final log:
`/tmp/yulang-runtime-resume-final.log`. No repeated broad workspace suite or
benchmark. A result of `11` alone does not prove exactly-once argument forcing;
the constructor/transition proof supplies that invariant.

Final source hashes are pinned in proof §12.1 (machine `3c80ef1c…`, receiving
`3d1ce66e…`, continuation `c1d71046…`); unchanged program/mod/test hashes are in
§10.1. Task/laboratory/index/README records are synchronized. The pending question
directory remains unstaged and uncommitted.

Remaining: full source materialization/entry timing, general negative/profile completeness,
nonprimitive consumers, missing source/library forms, native joint-result and
callback B correspondence, soundness/principality, default solver and F5 cutover.
