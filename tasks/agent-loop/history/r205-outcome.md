# R205 outcome — independent literal primitive boundary

Status: **R205 COMPLETE; exact semantic input gap independently reviewed; no parent root closed**

## Result

The sequential R199 candidate now records the R205 literal boundary at final SHA-256 `ba39a6f187c9c483ebbff06b74e7484526f2a208fdacb23a2f1ab08f28c0534c`. It does not invent an all-payload source rule or pretend the literal reflection equation is proved.

The source-rule syntax is already visible: `OriginalSourceGeneration.sourceRules` preserves the literal payload/site/context and its local declaration atom; R196 proves the corresponding symbolic `Build` formula. But this does not supply a concrete independent Simple-sub literal atom or its denotation. `OriginalSourceInterpretation.LiteralDeclaration` remains a supplied relation on `(literal, ValueRow)`, and its `Ground`/`valueForm` fields are supplied too. They do not determine which original literal rows the language accepts, nor map them to structural `Constraint.Satisfied`.

The selected typed-core schema says `Value(type of literal)` but does not fix the complete all-payload declaration and local relation. The selected SG rule requires the actual declaration and whole local typed relation, including alternatives and guards plus L1/L2 Return/effect/world obligations. The separately selected native `0` and `1` Call cases are bounded instances, not a whole-language table. R203 provides an eight-constructor payload-preserving PaperTypes type/value projection, but explicitly leaves its identification with the selected SG relation open.

Therefore the requested equations

```text
GenerateLiteralΣ(scope, occurrence, payload)
InterpretLiteralConstraintΣ(constraint, assignment)
ReadLiteralΣ(scope, occurrence, assignment)
```

remain a shape only until the independent literal primitive meaning is fixed. A local constraint interpreted as the supplied `LiteralDeclaration`/`Ground` relation would simply move that unspecified relation into `Solves`; interpreting it as source typing or the SG conclusion would be circular. No actual generated solution equation or soundness literal premise follows yet.

## Candidate definitions for the source-level decision

Two materially different candidates are now explicit, with no adoption:

1. **Intrinsic table:** select the R203 payload-preserving base type table for the eight constructors and define their descriptor/value/root embedding plus ground and Return laws. This fixes one intrinsic interface per constructor; it can reject original declaration alternatives with incompatible interfaces unless those are separately shown to be checks over that same interface.
2. **Declaration-driven table:** define the original declaration relation for each payload over its full descriptor/value/root/event row, including all permitted local checking alternatives, guards, ground and Return/effect/world obligations. This can retain multiple alternatives, but the actual table and local constraints still need to be specified and shown to match the original Yulang source rule.

These are candidates, not an exhaustive list or a user decision already made. Choosing one may affect accepted interfaces or alternatives, so the repository's design-authority gate requires explicit user approval before adoption. This is a missing input in the selected authorities, not evidence that the language has no semantics or that a new source decision is necessarily needed.

## Parent metric and execution

Parent delta: **0/4 roots; 0/5 packages**. No premise of the unchanged `InferenceSoundness` parent was removed. Coverage, principality and termination remain open. R204's earlier sufficient-direction clarification remains useful, but its candidate rule is still not connected to independent generated constraints and solutions.

No Lean, Lake, Rust, build or project test was run. No Rust source, pending question or quarantined path was inspected. No environment, cache, target, scratch or worktree was created.

## Independent review and next boundary

Read-only `spec_auditor` `/root/r205_literal_boundary_review` returned **PASS** on §4.3 at SHA-256 `4c30ab7904d179d43a56fd8f92b5d6580b5fbb4fb49a3250502fc92f4a38529d`, then authenticated the final status-line-only update to `ba39a6f187c9c483ebbff06b74e7484526f2a208fdacb23a2f1ab08f28c0534c`. It confirmed that the source artifacts support this stop, both candidates are accurately separated and unadopted, no source-semantics absence is overclaimed, and the parent delta is zero. Review was documentary; it is not a theorem or implementation proof.

R205 end dispatch selects a primary-owned concrete literal-rule proposal, not another theorem-target packet and not an immediate user choice between the two labels above. R203's intrinsic introduction may coexist with additional original declaration/checking alternatives. The proposal must specify descriptor/value interpretation, Return and intrinsic effects, admissible checking alternatives, and enclosing scope/witness; then compare it against the selected SG obligations and frozen source authorities. Show an existing-rule derivation or identify a concrete semantic commitment, ideally with a distinguishing typing/effect example. Only if a real accepted-meaning change is demonstrated does the design-authority gate require user approval before adoption. After the actual relation is fixed, construct and review generator/solution/readout equations; only then attempt application to the unchanged soundness parent.
