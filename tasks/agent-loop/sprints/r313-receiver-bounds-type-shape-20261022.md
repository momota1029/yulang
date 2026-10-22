# Sprint R313 — receiver-bound shape and FieldTail applicability

Status: ACTIVE, solo Luna primary; parent R149 remains OPEN.
Branch / baseline: `research/simple-sub-intrusion` / `805166211663097a76b867da68e05bd71a1b4d3a`.
Authority: unchanged user goal; unified design §§4.1–4.5, 6, 9 stage 4 and 10; proof companion §§3.2–3.8, 4.5, 7.2–7.4; R312 result.
Dispatch: degraded serial work because the user prohibits subagents. No independent proof or review receipt is claimed.

## Parent and measurable outcome

Keep the exact Yulang2 playground samples, pinned library sources and expected outputs. Continue the unchanged `Types` sample from its authenticated `pair.say` FieldTail obligation. R312 now retains the pinned ordered-pair implementation target `('a, 'b)` as a bounded structural shape and routes authenticated role/member candidates into the solver, but does not read saturated receiver bounds or select.

Derive receiver shape evidence from the same solver session after all ordinary source schedules have contributed their constraints. Join that evidence to the source-owned tuple target and the implementation's exact two `where 'a: Display` / `where 'b: Display` obligations without trial typing. Keep selection deferred unless the receiver frontier is complete and the unique applicable candidate is stable under every later admissible bound. If the current solver cannot prove that stability, retain the deferred boundary and establish the exact missing premise rather than selecting early. The immediate path must continue to the exact `Display.say` member graph and one same-use FreshUse once selection is justified.

Success evidence: a focused source-backed test identifies the exact ordered-pair target and its two generic role obligations, extracts the saturated receiver's ordered element evidence from the real session, rejects missing/ambiguous/inconsistent shape evidence, and establishes the stability rule or a concrete falsifier. A trial candidate type or a test-only receiver type is not evidence. The unchanged sample must advance beyond its present boundary or retain a precise source/solver owner gap.

This sprint does not close R149, whole-sample execution, Console, A/B, principality, termination, source/native correspondence, review, or production.

## Invariants and falsifiers

Preserve source occurrence, exact implementation identity, all actual effect contributions, and AV/AE/RE/RV coherence. Contravariant `[io]` denotes `[io,'e]`; `[state]` alone does not violate it. Do not choose from spelling, candidate order, a single partial bound, or a guessed principal type. Do not trial-type candidate bodies. Fail closed for unsupported target forms and unresolved where constraints. A later legal receiver constraint must not invalidate an exposed selection.

Falsifiers include an element-order swap, a missing tuple element, contradictory lower bounds hidden by SCC aliases, an unresolved generic `Display` obligation treated as solved, a candidate selected before the source schedules finish, or any changed pinned sample bytes.

## Exact leases and resources

Write leases: `crates/yu-hir/src/module/source_impl.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/candidate_extrusion.rs`, `crates/yu-solver/src/lib.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r313-receiver-bounds-type-shape.md`, and Luna-owned `tasks/agent-loop/current.json`. Other paths and pinned sources remain read-only. Expand leases before touching another owner.

Solo cap 1800 seconds, no carryover; one Cargo process at a time; focused checks at most 120 seconds. No workers or reviewers under the user's no-subagent instruction. Commit and non-forced push at coherent milestones; keep the tree clean.

## Stop conditions and continuation

When the source schedules have drained, inspect actual positive and negative receiver bounds, tuple structure, aliases, and their provenance before selecting. If the graph does not expose a complete stable frontier, preserve `DeferredSelectionUnavailable` and name the concrete missing solver readback or source-generated premise for the next sprint. Never change sample source, expected output, or method/effect semantics to force passage.
