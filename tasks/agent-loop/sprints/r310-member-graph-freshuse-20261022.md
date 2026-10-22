# Sprint R310 — member candidate graph and use-local FreshUse

Status: ACTIVE, solo Luna primary. Parent R149 and all proof/production gates remain OPEN.
Branch / baseline: `research/simple-sub-intrusion` / `0b48195c2276e1199d21b721f99a5924c8708d43`.
Authority: unchanged user goal; `notes/design/2026-10-20-r149-types-console.md`; unified design §§4.1–4.5, 9 stage 4, 10; proof companion §§3.6–3.8, 4.5, 7.1–7.3; R309 receipt.
Contract revision 1. Solo primary, no subagents per user instruction. R309 exhausted its 1800-second cap at the exact Member capture lifecycle boundary.

## Original outcome and success evidence

Preserve the unchanged Yulang2 Types and Console samples, pinned library closure, output behavior, and source/native obligations. R310 advances the R149 critical path by giving authentic member bodies a retained candidate graph and per-use FreshUse route, so member-owned nested FieldTail obligations are not rejected or shared globally.

Success evidence: (1) exact `SourceMemberRootId` identifies the retained graph and receiver parameter; (2) graph capture accepts only obligations with that exact Member owner; (3) every FieldTail's four Value/Effect rows are captured and mapped through one use-local FreshUse; (4) two uses receive disjoint local rows while preserving shared rows; (5) nested member obligations retain their exact member owner; (6) wrong/stale owners and duplicate routes fail closed. Advance unchanged Types beyond `DeferredSelectionUnavailable` only if a later same-session consumer can use stable bounds; otherwise state the exact next obstruction.

Open premises: role/implementation resolution, authentic receiver conformance, method body constraints linked to declared ports, stability of selection after relevant bound updates, nested `show` discharge, Console execution, source/native correspondence, A/B, principality, termination, independent review and production gates.

Non-goals: no fabricated top-level roots; no global member schedule execution; no cross-use row sharing; no selection from spelling or one observed tuple; no trial typing or rollback; no early readiness; no source rewrite or pinned-byte/output change; no semantic weakening. Contravariant `[io]` continues to mean `[io,'e]`, so `[state]` alone is not a violation.

## Continuing lanes

Proof: primary traces capture admission and FreshUse route ownership against the actual graph constructors. Reuse companion theorems only after their source-to-record premises are established. Solo evidence remains unreviewed.

Implementation: extend the existing definition-indexed graph lifecycle with exact member-root identity. Execute each member schedule once to form a template, then create every selected use through the existing per-use copying discipline; never expose the template's live rows as a use. Preserve owner identity for nested obligations. Do not implement the resolver before receiver/result/effect relations and stability are available.

Related stages permitted in this envelope: inspect graph/route owners; implement member graph indexing and capture ownership; retain member graph FreshUse per source obligation; add focused adversarial controls; run focused checks and unchanged Types boundary sample; record the next consumer gap. Source ownership must be reauthorized if it falls outside the exact leases.

## Permissions and resources

Exact write leases: `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, `crates/yu-solver/src/shadow_apply.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r310-member-graph-freshuse.md`, and Luna-owned `tasks/agent-loop/current.json`. Other paths are read-only. Do not edit HIR files unless a new exact authority boundary is created.

Solo cap: 1800 active seconds, no carryover; one Cargo process at a time; focused checks/tests at most 120 seconds each. No workers, no reviewer assignment under the user's no-subagent instruction. Tests are implementation evidence only. Stop on cap, user STOP, session end, semantic/source owner outside lease, or a genuine no-safe-code slice.

## Frozen seams and parent application

R309 established that `GraphState.graphs` and SCC execution are definition-indexed, and `capture_candidate_graph_inner` rejects non-Definition FieldTail owners. The member body is already retained as an exact Member schedule with an authenticated receiver endpoint, but no graph/FreshUse route exists. A template schedule may run once; its live rows cannot stand in for selected uses. R310's falsifier is any route that aliases a use-local row, drops one of four ports, weakens member ownership, or makes a nested obligation owner ambiguous.

The coherent result may be checkpointed as unreviewed research evidence only. R149 remains OPEN until both unchanged samples run with required outputs and all applicable source/native and theorem gates close. Luna alone stages explicit paths, checks the full outbound range, commits and non-forced pushes.
