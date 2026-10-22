# Sprint R324 — retain generic operator FieldTail obligations across FreshUse

Status: OPEN; Types remains deferred. This is a serial continuation after the R323 generic `+` obstruction.
Baseline: `c49d1bf44` on `research/simple-sub-intrusion`.
Authority: unchanged user goal, inference top-level principles, R149, and the converted Japanese design/proof documents. No sample/source/output edits or semantic weakening. User prohibits subagents; execution is serial and unreviewed.
Dispatch: `next_action_selector` is unavailable without subagents, so the primary records the concrete source-owner boundary directly. No agent is simulated.

## Parent and bounded outcome

Continue unchanged Yulang2 Types toward ordinary inference/execution while preserving the original source/native proof obligations. R323 established exact member identities, applicable override projection, and a one-FreshUse member consumer. Its solver attempt now reaches `lib/std/core/ops.yu` infix `+`, whose exact body is `\\x -> \\y -> x.add y`; while the generic provider is constructed, the `x.add` receiver has no positive source shape.

Determine where a FieldTail from a generic operator provider must live while the provider is abstract, then preserve that exact source obligation through enclosing candidate graph capture and activate it only in the concrete consumer FreshUse after receiver evidence arrives. Use one coherent row map for receiver/result/effect and preserve source owner, occurrence, role-member candidate IDs, and prerequisite evidence. Do not select early, erase an unresolved obligation, share constraints between independent uses, or turn ambiguity/incompleteness into a type error.

Success is unchanged Types inference reaching a new concrete boundary or successful inference, plus a falsifier for abstract and multi-use paths. If the required source/candidate constructor is absent, document the exact producer/consumer gap and keep Types OPEN.

## Evidence and falsifiers

- Trace exact operator provider root, nested `x.add` FieldTail source identity, operator use owner/occurrence, and parent scheme capture.
- An abstract generic provider retains the obligation without selecting an implementation or blocking unrelated module inference.
- A concrete consumer maps the same FreshUse rows and selects only with complete, unique receiver/where evidence.
- Two uses remain distinct; later evidence for one cannot contaminate its sibling.
- Incomplete inventory, unsupported target, negative bound, ambiguity, or missing prerequisite stays deferred.
- Preserve contravariant `[io]` as `[io,'e]`; `[state]` remains allowed.
- Original sample source and expected output remain unchanged.

## Exact write leases

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- this contract, `notes/theory/2026-10-22-r324-generic-operator-fieldtail-scheme.md`, and `tasks/agent-loop/current.json`

All other paths are read-only. At entry: `candidate_scheme.rs` 4547e13e5020e5a1050cd9c33d0a0312e36e392fff8a5c730f106e3b5217b365; `candidate_source.rs` 052f291acd7f33af9736663ccc38c01cfde0dda7433cff7a0d6fab04767babfb; `shadow_apply.rs` fd87ceda75cd230963c97b8a19426b52a93aae62fde476c8838f375aeee8bf20; `lib.rs` 1ec4517980dc542ed4477de47180c5336f8daa55915000d1ae306a1894c82795; playground `lib.rs` 773d4170cd3077e13867531506a4d6a150be849a4041b2b5beade9db3a1ef2d0.

## Verification and boundaries

Run focused source/scheme tests, `cargo test -p yu-playground --lib`, `python3 tools/agent_sprint.py check`, and `git diff --check` as each coherent step warrants. Tests and static checks are implementation evidence, not proof. Keep R149, source/native A/B, successful unchanged Types/Console, all samples, theorem closure, and production OPEN until independently established. Cap 2400 seconds, no carryover; commit/push coherent research checkpoints without force-push.

## R324 checkpoint evidence

The five retained pinned `+` uses are in `lib/std/core/fmt.yu` member roots and point to the same exact `std::core::ops` provider expression (`+`, body `\\x -> \\y -> x.add y`). Its abstract `x.add` receiver has no positive shape. Re-homing that obligation into the owning member template and adding a retry-after-progress FieldTail loop was a bounded prototype; the pinned readback then failed earlier with `Collection(MissingDefinitionEndpoint)`. The prototype was removed. After removal, `unchanged_types_sample_reads_receiver_bounds_from_its_pinned_module_session` passes again. R323's prior complete playground run was 42/42; the temporary R324 prototype run had 40 pass / 2 fail. No R324 inference success or theorem closure is claimed.
