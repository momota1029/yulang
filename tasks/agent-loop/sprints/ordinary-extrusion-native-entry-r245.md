# Sprint R245 — current ordinary extrusion entry and return

Status: ADMITTED for one bounded Sol-owned source-construction packet under the unchanged goal: Yulang inference soundness and its Rust implementation. Preserve the original parent theorem, all source forms, arbitrary independent satisfying assignment, and existing semantic choices. Parent delta remains zero until a checked source/native result is applied at its original edge.

## Fixed outcomes

R244's independent review passed its bounded account. The first missing constructor equation was identified at `candidate_source.rs:2316`: a successful `candidate_endpoint(Parameter(p), Positive)` translation must yield the branch-visible Value-positive term at allocated parameter row `parameter_live_base + p`. R244's pinned set omitted the defining owner. R70's historical conditional result also does not cover current Tuple/Record/Variant cases.

Sol must complete two separate, source-grounded sections in one theory note and handoff:

1. **Current entry construction:** trace initialization through `shadow_apply.rs` parameter and component translation, `live_value_term`, term arena construction, source/FreshUse/merge/transport, and the actual two `dispatch_live_item -> candidate_extrude` call sites. Derive each applicable entry-W conjunct from accepted production construction, preserving predecessor assumptions explicitly; identify the first unresolved equation if any. Apply derived facts at both actual calls.
2. **Current entry-to-return simulation:** independently trace current `candidate_extrusion.rs`, including Tuple, Record and Variant work/continuation cases, to determine exactly which return properties follow from the real call preconditions. Do not claim the older R70 proof covers new cases absent a complete case correspondence. Separate later acknowledgement/settlement and R71 raw-slot/canonical-fiber coverage.

A production-reachable malformed endpoint/term/view/owner/head is a falsifier only when constructed by accepted current paths and shown to reach an actual call. Hand-built states and tests are not falsifiers. If a required equation remains unavailable, record its exact defining owner and statement. Do not change compiler semantics or invent a replacement model.

## Assignment, inputs, outputs

One registered `prover`, Sol/high, no descendants. Exact write leases:

- `notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md`
- `tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md`

Pin and verify the R244 source manifest plus `crates/yu-solver/src/shadow_apply.rs` SHA-256 `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`. The R244 manifest is reproduced in its contract; source owners and R70 historical artifact hashes are pinned there. Also preserve baseline HEAD `5e228036817f6d1afe4271712dd6942790f26094`. If a dependency differs, stop citing it and report the mismatch.

No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths, or Git. Implementation lane remains NO_SAFE_CODE_SLICE absent a concrete reachable defect and a later exact repair lease.

## Resources and gates

Maximum 1,800 active seconds on current entry construction, then at most 1,200 seconds on current return simulation; total 3,000 seconds. Fresh independent `compiler_referee` review after both outputs freeze, at most 300 seconds. Each output must distinguish derived, conditional, and open facts, record exact dependency/output hashes and STOPPED-writing status, and state parent delta. Do not widen scope or depend on the unreviewed status of any worker. Luna owns current-state updates and integration.
