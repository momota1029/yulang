# R10 handoff — declared operation `perform` transport

Status: `SUCCESS_CHECKED_PERFORM_SLICE`; full paper theorem remains OPEN.
Baseline: `9cbf9feaf9a7b1548b4e98af3051fc24c2d8c715`.
Authority: `docs/yulang-operational-type-safety-ja.tex:241,953-977`.

## Result

`PaperExecutionSyntax.lean` now defines `OperationDeclarationResolved`: an
operation ID has a table member with that identity, and every member with the
same ID is equal to it. The new `PaperComputationTyped.perform` constructor
requires that exact resolution, matching type-argument arity, a payload typed
at the resolved declaration's instantiated payload type, and returns the
response type from that same declaration instance. This models paper `D(o)` as
a function; mere list membership is insufficient.

`OperationDeclarationResolved.typeTransport` preserves resolution under
`OperationDeclaration.substAmbient` and the operation list mapping in
`mapDeclarationTable`. The value recursor's computation motive now handles
`perform` by applying `operation_declaration_instantiation_subst`, transporting
the payload under the same mapped arguments, and rewriting the response type.
The previously exposed five arbitrary-σ transport theorems therefore cover the
new represented `perform` rule. The typing-local `argsSyntax_subst` helper was
renamed `typingArgsSyntax_subst` to avoid colliding with the imported
`DeclSubst.argsSyntax_subst`.

## Verification receipt

Pinned Lean: 4.35.0, Lake commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
One checker ran at a time with `-j1 -M1024`:

1. `lake build +YulangClosure.PaperExecutionSyntax` — exit 0, 7.2 s.
2. `lake build +YulangClosure.PaperExecutionTypingSubstitution` — initial attempt failed because the imported theorem is in `PaperTypes`, not a `DeclSubst` namespace.
3. Focused build — failed at the response projection; the commutation equality needed explicit projection normalization.
4. Focused build — same response mismatch while a patch command used the wrong relative path; no source change from that patch attempt.
5. Focused build after the explicit `OperationInstance.subst` normalization and response rewrite — exit 0.
6. `lake env lean -j1 -M1024 .lake/R10Audit.lean` — exit 0, 0.12 s.

Aggregate: 6 Lean/Lake invocations, approximately 9.8 checker seconds; within 8 / 120. `#check` printed the exact resolver-preservation theorem and all five complete transport types with arbitrary `σ`. `#print axioms` covered all five transports, resolver preservation, R9 support lemmas, `instantiateSubstitution_commutes`, and all three operation-declaration instantiation/instance transport lemmas. Results contain only `[propext, Quot.sound]` where required; several simple lookup/shape/field lemmas have no axioms. No `sorryAx`, `_f`, failed declaration dependency, or project axiom appeared.

Input receipts: syntax input at issue was `8ad8bc4b1549eadaa73c743438b333c62b44be7bdff0346f690b7da9e6353a97`; `DeclSubst.lean` was `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`; R9 handoff was `ac20f28dcfef58ec0389bd9da7382ae5033a3cc8190e640f2e42a8a98c10c04e`. Final implementation hashes are in `current.json`.

## Remaining boundary

This closes only the modeled `perform` constructor. `request`, handler arms, continuations, `mapOperation`, variants, nominal values, graphs, primitives, templates, patterns, and other paper constructors remain absent from the typing relation or transport proof. Term substitution, capture-avoiding renaming, full paper typing, inference/executor safety, original A/B obligations, source/native correspondence, and Rust bridges remain OPEN. R9 and R10 independent review are `NOT_RUN`; no self-review is claimed. No Rust or production source changed.
