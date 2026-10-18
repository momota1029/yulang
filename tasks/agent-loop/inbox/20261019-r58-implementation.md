# R58 Luna source-owner handoff

Sprint/contract: `original-name-prepublication-exposure-20261019-r58`, rev1, SHA-256 `87491930517debeea7c96baf14a74fe6cdd6a94dd8619554512ec672a6f71223`.
Baseline: `13e1e65da38e64992bc53f9e7f2cd2e12696ee3d`.
Role/author: `/root`, Luna primary, `current-conversation-2026-10-19-r58`; requested Luna/high, observed UNKNOWN/UNKNOWN. Read-only owner trace.

## Outcome and parent application

The exact top-level definition annotation is retained by HIR and satisfies the original forwarding theorem's constructor-level source-domain gate. Its whole-function type has a concrete `[io]` effect row on the Function argument and a separate `[io]` effect row on the result. The formal's own `[io]` Computation annotation is a third, separate position.

The ordinary candidate inference entry rejects the whole-function annotation during source preflight, before candidate batch collection, session creation, source action generation/execution, or any FreshUse. The precise obstruction is concrete negative-variance annotation effect rejection in `candidate_source::preflight_annotation` and the matching `candidate_signature_effect` guard. No native provider rows are allocated or physically changed, and the requested pre-publication exposure transition cannot be observed for this exact case.

This is candidate compiler unsupported coverage, not a language-source exclusion, successful-prefix result, source-qualified parent counterexample, or evidence of annotation compatibility. Parent forwarding preservation and Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED. No production conclusion follows.

## Source/native owner chain

- HIR binding/parameter annotation retention: `yu-hir/src/module/local_source.rs`, `module.rs`, `module/source_annotation.rs`.
- Definition-level candidate preflight before collection/session: `yu-solver/src/shadow_apply.rs:385–435`.
- Whole-source annotation negative-row refusal: `candidate_source.rs:451–459,603–615`.
- Unreachable Action::Annotation emission/dispatch on this route: `candidate_source.rs:1455–1465,1693`.
- Matching native annotation constructor refusal if reached: `candidate_effect.rs:1740+`, `1933–1935`.
- There is no generated-constraint/propagation/consumer route for this exact candidate because preflight fails first. No fake physical alias is inferred from source positions.

## Evidence, checks and limits

Static inspection plus contract dependency SHA checks only; 22/22 dependencies matched at activation and on the Sol active-work receipt. No tests, builds, parser execution, solver/compiler/runtime, probes, measurements, code changes or expected-output changes. Duration/CPU/RSS and observed settings UNKNOWN. The exact artifact is `notes/progress/2026-10-19-r58-provider-publication-owners.md`; its SHA-256 is recorded at freeze.

The candidate is fixed under rev1. Any alternate annotation or bypass needs a new dispatcher decision, contract and pins. Sol owns the disjoint proof artifact/handoff. Luna's outputs are frozen after this handoff; fresh independent compiler and spec review remain pending.

Worker state: primary source trace complete; writes stopped after hash/freeze. No descendants. Commit/integration pending independent review and closeout.
