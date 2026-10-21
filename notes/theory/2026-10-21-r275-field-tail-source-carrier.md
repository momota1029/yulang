# R275 — FieldTail source carrier

Status: provisional HIR/source-consumer step; primary-only and unreviewed. Contract revisions 1–2 add the solver and runtime-program consumers after direct-dependent builds identified exhaustive matches. R149 Types/Console and all sample/proof/production gates remain OPEN.

## Parent application

The unchanged R149 Types source reaches the current parser, and its binding-only prefix (including ordered tuple construction) passes candidate inference. The exact final `pair.say` root returns `unsupported source`; the same expression in a binding returns `StructuralProjection`. The existing ordinary local-source builder handles application tails but not `SyntaxKind::FieldTail`. The older ShadowArtifact retains parse-owned FieldTail and associated receiver nodes, showing an existing source owner and identity convention to follow.

This step will add a source-carrier node for each FieldTail with the original receiver relation, member spelling/range, and tail source key. This is syntax/source evidence only. It does not resolve Display, import or select a library implementation, infer a type, or establish output.

## Verification

The focused HIR carrier check passes for the exact Types source and chained `base.first.second`, preserving the `pair` receiver and parse-owned `say` token. After adding the solver and runtime consumers, `cargo check -p yu-playground` passes. The solver visits the receiver then returns `Collection(ComponentIdentityExhausted)` at unresolved FieldTail construction; the runtime adapter carries an explicit `UnsupportedFieldTail` boundary and its handler-range walk descends through the receiver. The exact unchanged Types CLI sample still fails before execution with that candidate-collection unavailability. Sample inference and execution remain OPEN.

## Implementation result

`LocalSourceForm::FieldTail` retains the receiver index, member spelling and token range; the enclosing `LocalSourceExpr` retains the original tail source key and occurrence. Chained tails preserve `base -> first -> second`. Candidate collection visits the receiver and withholds the candidate until authentic method/field resolution supplies a relation. Runtime also refuses direct construction without that relation. This records source syntax faithfully without treating `say` as a builtin or accepting an unknown field.
