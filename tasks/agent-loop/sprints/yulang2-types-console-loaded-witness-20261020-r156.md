# Yulang2 Types/Console loaded-registration observer — R156

Status: prospective bounded contract; Luna activates the preparation grant after exact-hash independent review. The existing user goal is the authority to continue this proof-backed implementation work. This contract does not authorize sample execution, tests, builds, semantic changes, expected-output edits, or production cutover.

## Goal and preserved parent

Continue the active goal: proof-backed Yulang inference/evaluation and broad unchanged Yulang2 Web sample support. Types/Console remain an increment rather than a compatibility ceiling. Preserve `notes/design/2026-10-20-r149-types-console.md`, original Simple-sub/evaluator A/B claims and quantifiers, source/native correspondence, semantic approval, expected-output protection and independent review. All parent gates stay OPEN; `WAITING_NO_SAFE_CODE_SLICE` applies to Y3 production implementation.

Y3 baseline: commit `85586bb7343b41f286f34b937f2d8e99e8629ced` (working tree has the previously recorded research artifacts; do not clean, reset, stash, or stage unrelated paths). Y2 oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, read-only worktree `/home/momota1029/rust/yulang2-choice-recollection-trace`. Sample owner: `web/playground/src/main.ts`, blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`; use only the exact R149 40-library closure.

Predecessors: R155 closeout `notes/progress/2026-10-20-r155-closeout.md`, SHA-256 `a914dd2d0e6127dbfd80ed6201784f8c7d347b8fda6ebb63fa79ba5002704720`; R154 closeout SHA-256 `45413f2e896fdd50ad4761cd6a4572a7a993a3f8b33a54664416e40f79f76ea5`. Reuse only reviewed R152 constructor, R153 declaration-shape and R154 registration/query relations within their stated premises. Exact sample parsing, complete declaration census/order, specialization, Request reachability, and all parent theorem obligations remain OPEN.

## Stage A — exact observer packet, 240 seconds

Read-only preparation. Pin and review the exact source blobs and relevant functions in:

- Y2 `crates/sources/src/lib.rs`: `LoadedFile`, source load entrypoints, and the `LoadedFile` construction after `parse_module_with_optional_timing` (R155 pinned blob `38d85d7dbb76bca11917963af52f72b17769e3c8`). Its retained `op_table` is the initial table passed to parsing; parser-local operator updates occur while producing the CST. Record this as initial loaded-table identity/content. Do not label it the evolving parser state or final parser environment unless a pinned actual producer exposes that state.
- Y2 `crates/yulang/src/source/mod.rs`: source collection/loading and lowering handoff (R155 pinned blob `6472d8fb4268bdd08757eef4aeaf1bf65fedc2b0`).
- Y2 `crates/infer/src/module_map/mod.rs` and `crates/infer/src/module_map/finish.rs`: actual loaded-source registration callers of `insert_value_with_span` (pin exact blobs before implementation). Record caller provenance at these source producer seams; the shared `insert_value_with_span` method is not source-specific because `crates/infer/src/module_table/compiled.rs` also calls it.
- Y2 `crates/infer/src/module_table/mod.rs`: `ModuleTable` declaration and shared `insert_value_with_span` storage operation (pin exact blob before implementation).
- Y2 `crates/infer/src/lib.rs`: `ModuleTable` storage identity (pin exact blob before implementation).
- Y2 `crates/yulang/src/main.rs`, `support.rs`, and the exact sample/library inputs only if the chosen minimal observer needs those owners; use R155/R149 pins and record every additional blob before writing.

Produce a frozen exact implementation packet naming each modified path in an isolated copy under `/tmp/yulang2-r156-observer/`, the exact new observer entrypoint or narrowly gated instrumentation, output schema, no-semantic-change argument, sample and library byte hashes, one future invocation (not run in this sprint), failure/partial-output rules, and owner for removing the scratch copy. The observer must capture actual loaded `module_path`, `band_path`, source bytes/hash, initial loaded operator-table identity/content, actual CST/declaration source identities, and ordered source registrations `(module,name,DefId,order,visibility)` at their producing seams. Preserve duplicates and distinguish source insertion from compiled-surface insertion by source caller provenance; the shared insertion method alone is insufficient. Distinguish the initial loaded table from parser-local operator updates during parsing; claim the latter only if a pinned producer actually exposes it. No inferred or display-reconstructed event may be labeled actual.

No parser/sample/test/build execution, code modification, instrumentation, or scratch creation during preparation. If faithful observation cannot fit these pinned seams, freeze the exact limitation and stop this stage.

## Stage B — independent packet review, 120 seconds

Fresh reviewer evaluates exact source/blob pins, observation completeness and event ordering, input identity, source-vs-compiled separation, noninterference, output schema and cleanup/lease boundaries. Any correction creates a new frozen revision and invalidates review of changed bytes. CLEAN review authorizes Luna, acting under the active user goal, to issue the conditional provisional-observer implementation grant below; no further user confirmation is required for this bounded reversible research instrumentation.

## Stage C — conditional provisional observer implementation, 360 seconds

Issued only after Stage B is CLEAN and Luna records the exact grant and frozen packet hash. Writer owns only the exact source files and output paths named by the reviewed packet inside `/tmp/yulang2-r156-observer/`; no Y3 production paths or Y2 oracle worktree writes. Implement the smallest reversible observer that records actual values at load construction and source registration. Keep it isolated and explicitly provisional. Do not run it, build it, run tests, alter expected outputs, or promote its interface. If implementation reveals a missing owner, behavior change or required broader edit, stop and return that exact blocker without expanding the lease.

## Stage D — frozen code review and closeout

Independent review (120 seconds) checks the exact diff for completeness, omitted/generated/interleaved event risk, preservation of constructor behavior, source identity, duplicate registrations, compiled-route separation and agreement with the reviewed R154 cursor relation. No execution review is included. Closeout (120 seconds) records hashes, grant/review receipts, exact resource accounting, cleanup status and remaining evidence. Retain the bounded patch as a frozen provisional candidate; do not delete it before Luna has preserved its hash and explicit cleanup decision.

## Resources and boundaries

Fresh R156 cap: 960 seconds: 240 preparation + 120 packet review + conditional 360 implementation + 120 code review + 120 closeout. Charge only issued allocations. Astra 0; no carryover. No tests/builds/sample executions are authorized by this contract. A later sample witness execution requires a separate concrete invocation, resource limit and Luna authorization. A generated witness proves no inference acceptance, runtime output, semantic approval, parent theorem closure or production readiness by itself.

Only Luna owns `current.json`, exact lease grants, independent review assignment, adjudication, staging and Git. Parent gates remain OPEN unless independently proved at their original scope. Next consultation: a source contradiction, missing observer owner requiring expanded authority, frozen code review seam, or sprint end.
