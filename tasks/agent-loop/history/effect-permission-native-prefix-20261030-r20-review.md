# R20 independent review

Reviewer: `/root/effect_permission_native_prefix_r20_review` (`compiler_referee`)
Disposition: **ACCEPT the frozen failure checkpoint as `CLOSED_INCOMPLETE — COMPILE_BLOCKED_BEFORE_RUNTIME`**. No blocking finding against preserving the failed experiment and general Lean model. Two major limitations block reusing the instrumentation as source/native correspondence evidence.

## Authentication

- R20 input manifest revision 2 (`ef67605cf9ed126de83d1cd434bee8afe2d86b43c38d6d2dcb31538fcb5150f4`): all 28 nonmutable entries match. Historical `current.json` and mutable isolated admission copies were appropriately excluded.
- All five final Rust source hashes, the Cargo receipt (`fa0b472bd0ce7477f8d082872439da3158e7f2d2c0fe92e9a46cc40a598e4e27`), both handoffs, seven Lean evidence hashes and all 18 dependency hashes in both Lean trees match.
- Raw Cargo streams show exit 101, empty stdout, four compilation errors and no test execution. `SourceAnnotation.text` and `RoutePurpose: Debug` were corrected after the command; those corrections remain uncompiled. The remaining dependency mismatch is `Graph.formal_capture_trace_id` at isolated `candidate_scheme.rs:214` versus omitted fields in detached `shadow_apply.rs:4951,5064`; recorded detached and main-tree hashes match.
- `machine_trace` is null and all 21 R18 fields are unavailable. No selected occurrence, arena state, source-plan event, native call or runtime counterexample is authenticated.
- First missing edge: a compiled test executable reaching the ordinary source route. Repairing the two `Graph` initializers is necessary, but this failed invocation cannot establish that the corrected final sources have no further compilation errors.

## Major findings for a successor probe

1. **Same-call identity is not enforced.** In isolated `candidate_source.rs:2548–2554` and `term.rs:1374–1385,1479–1488`, assertions independently search the whole trace for event names and `journal_present:false`. Events from separate invocations could satisfy those checks. Term events lack an explicit arena/invocation identity bound to the selected occurrence. A successor must add that association or justify an unambiguous event interpretation, then check the selected call's fields and prefix structurally.
2. **Session journal removal is not observed at its owner transition.** In isolated `lib.rs:9590–9593,9612–9619,9770–9784` and `FormalPermissionNativePrefix.lean:73–78`, success first observes after session `.take()`. Rollback has one observation before `.take()`, then arena events occur without a session-removal observation. The stream does not directly supply before/after observations for model action `takeSession`. A successor must observe around `.take()` or explicitly distinguish source-reconstructed transitions from observations and prove their order and owner association.

These findings do not change R20's failed-execution disposition. Both remain explicit blockers before any future trace is accepted.

## Lean review

- `FormalPermissionNativePrefix.lean` (`7129aae721bf07eeb9330540c833a3b7d6d225dea8dc9e722b6e207e2bbef0f1`) matches its audited isolated copy.
- Raw audit 1 confirms Lean 4.35.0 and four successful roots: `transition_projection`, `run_projection` and `initial_projection` are axiom-free; `validates_cons` uses `[propext]`.
- No concrete event list, selected-call state derivation, completion equality or application of R19 `selected_call_excludes_R18` exists. The general projection theorem also holds for unvalidated lists and supplies no native authentication.
- Audit receipt reports exit 0, 20.98 seconds and 971,900 KiB maximum RSS. The former `/tmp` construction path and helper scratch exception are disclosed. Reviewer read the raw evidence and did not rerun verification.

Source/native correspondence, the original parent theorem and production conformance remain OPEN. Reviewer made no writes, Git operations, compiler/checker runs or descendants; work stopped.
