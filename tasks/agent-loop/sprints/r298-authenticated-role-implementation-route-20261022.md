# Sprint R298 — authenticated role-to-implementation source route

Status: CHECKPOINTED_UNREVIEWED, solo serial primary; no independent review or theorem closure is claimed.
Branch / baseline commit: research/simple-sub-intrusion / b7393fc112b92aed38ceeff87db166881d1ebe4e
Authority: unchanged R149 Types/Console source and outputs; unified design §§3–5, 7.4–7.5, 9 stages 2 and 4; proof companion §§7.1–7.2, 7.5. R297 authenticated imported SourceRoleId carrier.
Contract revision / primary approval: R298. User's persistent implementation/proof goal authorizes the work. Solo mode follows the explicit no-subagent instruction; next-action dispatch is omitted under that instruction.

## Original outcome and success evidence

Parent remains Authoritative R149 unchanged Types (142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`) and Console (92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`) with their exact inferred public types, source-order host output and runtime behavior. R149, source/native soundness, principality and production remain OPEN.

This sprint establishes the next source premise: an exact imported `SourceRoleId` resolves to the exact non-recovered implementation declarations and member source identities in the authentic provider module. For the pinned `Display` role this includes primitive and ordered tuple implementations. Missing, duplicate, stale, recovered, or unsupported role heads fail closed. The result is a candidate inventory only; it does not select an implementation for an inferred receiver or discharge a `where` obligation.

Implementation goal: `SourceRoleId -> provider module index -> implementation declaration/member identities`, retaining module and parse-owned source keys. A focused regression must falsify same-spelling cross-module or duplicate-module substitution. Existing Y2 files and expected output remain byte-for-byte unchanged.

## Proof and implementation work

- Source-correlation lane (Luna, serial): define the exact identity premises, implement role-index lookup, and test successful and fail-closed paths using the pinned `std::core::fmt` source index.
- Candidate integration (Luna, serial): trace how the resolved inventory can be attached to the retained `SourceRoleObligation` and its existing same-FreshUse subject row. Do not consume the inventory for type-directed selection until provider schemes and receiver-type evidence exist.
- No Astra or subagents under the user's solo instruction. No independent review is claimed.
- Preflight remains closed for nonempty `where`, imported Names, and `FieldTail`. No spelling-based method special case, source rewrite, test expectation weakening, or production promotion.
- Continue within this contract through the source-owner/member correspondence and its negative identity controls. Return to a new material dispatch boundary before imported scheme assembly or semantic selection.

## Exact paths and resources

Read: R149 authority, the two converted design/proof Markdown files, R282, R295–R297, and exact owners below.
Write leases: `crates/yu-hir/src/shadow.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r298-authenticated-role-implementation-route.md`, and primary-owned `tasks/agent-loop/current.json`.
Resource envelope: 1200 seconds, one primary process at a time, one Cargo process at a time; no background work. Checks: focused `yu-playground` tests plus `cargo test -p yu-playground` if implementation remains localized and resource behavior stays ordinary.

## Stop and handoff

Stop this slice if the exact role-to-implementation relationship cannot be established from retained source identities without assuming type-level conformance. Record the precise missing source/consumer premise and keep preflight closed. Otherwise freeze the source correspondence, commit and push the coherent paths, synchronize current state, and name imported scheme construction plus same-world FreshUse consumption as the next open implementation seam. No whole-compiler proof follows from source lookup or green tests.
