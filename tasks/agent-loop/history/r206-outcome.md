# R206 outcome — intrinsic literal-rule proposal

Status: **R206 COMPLETE; concrete rule proposal reviewed PASS; proposal not adopted**

## Proposed source rule

The R199 model candidate is at final SHA-256 `c09ff5efaa756989adb4b5cd0977c514b02a987705e40cb72a06ebd633948525`. Section 4.4 gives a concrete proposed source rule over all eight raw payload constructors, reusing R203's exact payload-preserving mapping and its base type table:

- `unit → Unit`, `bool → Bool`, `int → Int`, `floatBits → Float`, `string → String`, `bytes → Bytes`, `path → Path`, `character → Char`;
- source value is `PaperTypes.Value.literal(p(l))` with the raw payload unchanged;
- the proposed descriptor is `Value(τ(l))`;
- the source row uses a proposed literal-origin root `LiteralRoot(q)` at the original occurrence and the inherited ambient event `e0`; it does not obtain these fields from the solver assignment;
- `Return` preserves value/root/event and produces `Comp(empty, τ(l))`; literal intrinsic performed effects are empty. Enclosing permission, inflow, residual, Call effects, guards and futures remain in the contextual judgment.

The checking grammar uses the selected Source-Generalize §3.2 proof constructors: base introduction, finite same-value/checking derivations, actual annotation/final formation, and independently registered method/adapter alternatives with full input/output relation, guard, effects and source boundary. Proof-only checks keep the base row. Executed conversions have their own endpoints and event transition; they may produce another row/effect but stay linked to the original occurrence and the same outer witness strategy. The proposal does not derive a method from a matching printed type.

## Review and authority disposition

Read-only `spec_auditor` `/root/r206_literal_rule_review` returned **PASS** on the corrected §4.4 at SHA-256 `11d489e9152f9ed9c1697b0ddc916b7118b0a271c8128a0577410008e7baac5e`, then authenticated the final status-line-only update to `c09ff5efaa756989adb4b5cd0977c514b02a987705e40cb72a06ebd633948525`. It confirmed the eight payload/type equations, intrinsic-versus-contextual effects, separate solver/source witness fields, conversion event/effect handling, and that the `Number` example is only hypothetical. The earlier major findings about source-assignment operands and conversion endpoints were corrected; the minor `e`/`e0` mismatch was fixed.

The review also confirmed a remaining adoption gate: `LiteralRoot(q)` is still a proposed source provenance constructor requiring an authentic L1 justification and the later `sameScoped` readout. The selected authorities do not derive this root law or show whether an unregistered overloaded literal declaration exists. R203 expressly makes its base introduction nonexhaustive; SG §3.1 still requires the actual declaration and all original alternatives/guards. Therefore the candidate is **not adopted** and is not yet proved equivalent to the original Yulang literal rule.

The `int → Number` case in §4.4 is a discriminator only: it shows what would change if such an unregistered literal alternative is part of the original source language. The inspected sources do not establish that it is. The concrete proposal makes the previously abstract boundary reviewable, but it does not by itself establish an actual semantic conflict or justify choosing new semantics.

## Parent metric and execution

Parent delta: **0/4 roots; 0/5 packages**. No premise of the unchanged `InferenceSoundness` parent was removed. No actual Simple-sub local atom, independent solution denotation, generator/readout equation, literal reflection theorem, or `sameScoped` application was produced. Coverage, principality and termination remain open.

No Lean, Lake, Rust, build or project test was run. No Rust source, pending question or quarantined path was inspected. No environment, cache, target, scratch or worktree was created.

## End dispatch and required user input

The proposal now exposes a specific semantic decision boundary. To proceed without changing the original source meaning, the next input must identify the original L1 literal-root/declaration rule and any admitted unregistered alternatives (for example, their authoritative source table). If no such alternatives are part of Yulang, the user can explicitly approve the proposed intrinsic table, `LiteralRoot(q)` provenance, and rule that additional literal-specific conversions require independent registration. Approval is required before adopting that commitment. After the original rule is fixed, construct the actual Simple-sub local atom and independent denotation; only then is solver reflection eligible.
