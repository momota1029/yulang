# Yulang3 explicit-execution proof progress — 2026-10-26

## Scope and provenance

The current user request authorizes proof development and push on `yulang3`.
Construction began at `de9d8e5164647bc777101f07a392992c98d4bb87` in an isolated
checkout. Incoming R56–R58 records were retained through `00194ec58`.
These modules are fresh constructions, not recovered R55 candidate bytes;
historical failed audits and withdrawn questions retain their status.

Source: `docs/yulang-operational-type-safety-ja.tex`, with its opening
corrections and `notes/theory/2026-10-24-corrected-core-value-continuation.md`.
The results below concern the represented explicit executor. Full language
progress, effects/lifetimes, source/native correspondence and original
Simple-sub A/B obligations remain OPEN.

## Accepted results

### Type application

`PaperTypeApplicationPreservation.lean` proves cancellation after inserting an
arbitrary block of type binders and instantiating it with the actual arguments.
It covers all existing raw syntax families, metadata and the complete
declaration table, including nested binders and formal-binder template bodies.

`instantiate_body` consumes `PaperValueTyped.subst_explicit` and restores the
identical declaration, graph and lexical environments. `typeBetaValue_preservation`
and `typeBetaForce_preservation` prove the actual beta redex; `force_typeBeta_delay`
also proves the distinct subsequent Force/Delay endpoint. Continuation response
and result types are independent. No closed-context restriction or assumed
preservation law is introduced.

Source SHA-256: `60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556`.

### Registered templates

`PaperTemplateExecution.lean` implements a finite Nat-key lookup and one body
expansion, checking both type and value arities. The unchanged unique complete
entry resolver identifies the actual selected code body.

`BodyTyped` checks the registered body once in the reversed formal environment;
`BodiesTyped` requires this for every table member. These are independent
syntax-directed derivations, not assumptions of execution safety. All captured
term/graph values are explicit arguments, as the manuscript requires.
`BodyTyped.instantiate` consumes cancellation; `BodyTyped.expand` then performs
graph weakening and simultaneous term substitution. `template_applicable` and
`template_preservation` apply these lemmas to the existing invocation judgment
with arbitrary caller graph and lexical environments. A two-type/two-value
example distinguishes formal order and checks the actual expansion.

Source SHA-256: `3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792`.

### Repeated response/resume and failure

`PaperCombinedExecution.lean` retains every successful existing core/let,
tuple-split, perform and request-bind transition and adds empty-owner raw
resume plus failure unwinding. The exact failure reason is preserved.
`finite_prefix` applies to actual successful `controlStep` equations;
`finite_interaction` also admits arbitrary interleavings of external responses.
Its separate protocol checks only each foreign response at the actual request
instance's response type, never assuming an internal preservation law.

`shared_continuation_prefixes` reuses the same immutable saved continuation.
`example_arbitrarily_many_rounds` constructs actual perform, request-bind,
response, resume and split transitions for every natural number `n`, proving
exactly `n` responses and `n` resumes. It then applies the general preservation
theorem to that family. Nonempty-owner cases remain explicitly unsupported;
`none` is not identified with a safe terminal result.

Source SHA-256: `58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1`.

## Verification and review

Official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Lake `5.0.0-src+eb6cafb`; release archive SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Pins/manifests were unchanged. Each native call used one Lean thread,
`-j1 -M1024` and a 120-second process-group timeout; no timeout occurred.

Both targeted module builds passed. All 36 type-application declarations
(27 public, 9 private) and all 12 template declarations passed theorem-kind,
exact type and complete axiom audits. Actual private names were constructed
with `Lean.mkPrivateNameCore`; exact counts and ordered output were checked.
The two nested-type examples use no axioms; other type-application results use
`propext` and `Quot.sound`. Template lookup uses `propext`; other template
results use `propext` and `Quot.sound`. There is no `sorryAx`, custom axiom,
native-evaluation assumption or checker bypass. New modules have zero warnings.

Fresh independent reviewer `/root/proof_review` inspected both frozen sources,
the unchanged direct dependencies, original source meaning and every type/axiom
block, and returned CLEAN with no blocking/major finding. The reviewer authored
no proof and made no checker call. This accepts the local statements only.

The combined module also built without new warnings. All 37 authored theorem
declarations passed the repository checker; a further audit enumerated all 87
theorem constants, including 15 generated private helpers. Their axiom groups
are 69 with `propext`/`Quot.sound`, 6 with `propext`, and 12 with none. The same
fresh reviewer inspected all 87 complete type/axiom blocks, unchanged inputs,
and the frozen module, returning CLEAN for preservation and erasure only.

Unchanged lint/deprecation warnings belong to the existing
`PaperExecutionSyntax`, `PaperExecutionBinderLaws`, `PaperTermSubstitution`,
`PaperCoreStep` and `PaperTupleSplitExecution` owners. Cleanup is deferred while
these shared inputs are frozen and a separate remote audit owns the same
snapshot. No warning suppression or new warning was introduced.

## Next integration and remaining obligations

This checkpoint preserves the checked local modules. Default-root integration
and the concrete combined execution theorem are in progress. The next stage
consumes type beta and templates with repeated empty-owner resume and literal
failure propagation, proving the actual function's every successful transition
and finite interactions without an assumed `LocalLaws` instance.

Still open: remaining principal/context constructors, nonempty-owner freshening
with immutable evidence identities, graph guardedness, source/native realization,
whole-language progress, inference soundness/principality/termination.
The existing `CallProgressObstruction.reachable_typed_viewed_force_stuck` and
`FreshHeap.self_alias_payload` prevent promoting partial preservation to full
progress. Withdrawn semantic questions remain untouched.
