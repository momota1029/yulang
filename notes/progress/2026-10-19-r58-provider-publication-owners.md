# R58 primary source-owner trace: definition annotation preflight obstruction

Sprint: `original-name-prepublication-exposure-20261019-r58`, rev1
Contract SHA-256: `87491930517debeea7c96baf14a74fe6cdd6a94dd8619554512ec672a6f71223`
Baseline: `13e1e65da38e64992bc53f9e7f2cd2e12696ee3d`
Primary/author: `/root`, session `current-conversation-2026-10-19-r58`
Claim class: bounded read-only source/owner obstruction; not a source-qualified counterexample or theorem result

## Fixed source and parent-domain check

The exact candidate is:

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

At the source-constructor level this remains inside forwarding-preservation §1: `forward` has one explicitly annotated Computation formal, its body is the resolved direct formal Name, and `outer` supplies the whole current formal as a first-order argument. `outer` adds no function-valued forwarding argument. The source's incoming effect stays open; its `[io]` permission is not treated as a closed incoming cap. This is the same constructor-level eligibility the dispatcher confirmed. It is not evidence of candidate typing, annotation compatibility or native success.

## HIR retains the annotation; candidate preflight rejects it

HIR formation retains the top-level binding annotation on the definition source (`module/local_source.rs:1266+`; `module/source_annotation.rs:317–377`). `plain_binding_header` accepts a single named argument with its parameter annotation under the local-source mode (`module.rs:2937–3065`). `parse_type_source` parses a bracket row on the left side of an arrow as the Function argument's `effects`, and parses the arrow result recursively (`source_annotation.rs:409–503`). Therefore the whole-function type annotation has this tree:

```text
Function.argument.effects = [io]
Function.result.effects   = [io]
Function.effects          = None
```

The formal's own `[io]` Computation annotation is a distinct `LocalSourceParameter.annotation`; it does not change those whole-function positions.

The candidate solver refuses before it constructs or executes any action. `CandidateInference::solve_mode` iterates source roots and calls `candidate_source::preflight` before `ConstraintBatch::collect_candidate_mode_scoped` and before `InferenceSession::try_new_candidate` (`shadow_apply.rs:385–435`). `candidate_source::preflight` rejects a root annotation when `preflight_annotation(annotation.ty, true)` returns false (`candidate_source.rs:451–459`). At `candidate_source.rs:603–615`, a Function argument recursively flips variance; a concrete row at negative variance returns false. Here the left `[io]` row is exactly that negative concrete row, so preflight returns `CandidateError::Unsupported`.

This is not merely a schedule question. The later `Action::Annotation` emission in `candidate_source.rs:1455–1465` and dispatch in `:1693` are unreachable for this input through the ordinary candidate entry point. The independent consumer also rejects the same case at `candidate_effect.rs:1740+`, at the `variance == Negative && !row.concrete.is_empty()` guard (`:1933–1935`). Bypassing either guard would change the authorized route; no bypass or executable probe was attempted.

## Exact owner transition and limitation

The owner transition is the early `solve_mode -> candidate_source::preflight -> Unsupported` return, before batch collection. Thus this candidate produces no native `Action::FormalEntry`, `Action::FormalNameEffect`, or `Action::Annotation`; no candidate inference session; no original live Function/AE/Name/RE rows, levels or nongeneric metadata; no annotation-driven physical write; and no first authentic `forward` capture/FreshUse. Source HIR endpoints and names cannot be promoted to native rows or physical aliases.

Result: the requested pre-publication exposure trace is blocked by an exact candidate-compiler constructor guard. No successful compatible constructor prefix for this annotated case was established, so it is not a valid positive exposure witness or parent falsifier. The HIR/source input remains in the original theorem's domain; this finding is not a language-level exclusion and does not change the parent quantifiers or semantics.

The fixed contract allows this exact compatibility obstruction to be frozen. It does not authorize changing the annotation, relaxing preflight, invoking the parser/solver/compiler, or trying a new candidate. A different source annotation would require a new dispatcher decision/contract and new pins before work.

## Evidence boundaries and handoff

Static source inspection and hash checking only. No parser execution, tests, builds, solver/compiler/runtime, probes, measurements or code changes. Actual runtime duration/CPU/RSS and observed model/effort are UNKNOWN. The primary trace is read-only; the separately leased Sol proof and handoff remain the independent lane outputs. Original forwarding theorem, Simple-sub A/B and production remain OPEN 0→0; R50 remains NOT ADOPTED.

Primary handoff: `tasks/agent-loop/inbox/20261019-r58-implementation.md`.
Next step: freeze the Sol result and handoff; obtain fresh compiler and spec reviews; then consult the dispatcher at sprint close for a materially compatible next gate.
