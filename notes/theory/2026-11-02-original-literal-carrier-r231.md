# R231 original literal carrier and solution readout

Status: **MODEL GATE IN PROGRESS**. This is primary-owned source-model work
under R231, baseline `c5cc9682aa2f4cb90a64d595202adc28ec570887`. It is not yet
a Lean theorem, a model-completion claim, or a parent-root reduction.

## Unchanged parent edge

`SourceProblem.InferenceSoundness` remains unchanged in
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`. At the literal
induction edge the required implication has this shape:

```text
original source literal l at (q, r, e₀, ξ, ω)
  + independent generated Value/Effect constraints d_l
  + arbitrary assignment a satisfying d_l
  ⇒ the adopted literal source row and pure Return
     at the SAME q, r, e₀, ξ, ω and shared witness ω.
```

The implication may not take `LiteralAtom`, the source declaration, a source
judgment, a readout law, or the desired descriptor/effect conclusion as an
input. The source constructor itself fixes the raw value; the independent
assignment must supply the descriptor/effect facts through the actual model.

## Fixed source rule

The adopted L1 authority fixes all eight raw constructors and their complete
payloads, with `τ(l) = PaperTypes.literalType(payload(l))` and
`v(l) = PaperTypes.Value.literal(payload(l))`. Its intrinsic descriptor is
`Value(τ(l))`; its intrinsic Return is `Comp(empty, τ(l))`. It retains the
original root coordinate `r`, event `e₀`, occurrence `q`, scope `ξ`, and one
shared witness `ω`. It does not erase contextual permission, inflow, residual,
Call, guard, future, checking or conversion obligations. Synthesis and an
annotation's written target remain distinct.

Authority pin:
`notes/design/2026-11-02-literal-l1-adoption.md`, SHA-256
`f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`.

## Existing structural evidence

`AbstractGeneratorDenotationR220.literalStructuralFragment` has two reciprocal
Value atom bounds and one Effect-to-bottom bound. Its checked
`literal_structural_readout` proves exact graph-node readout at the supplied
variable coordinates for every satisfying regular graph store. Its
`literalCode` distinguishes the eight literal constructors, while deliberately
not encoding raw payloads. That fragment has no equation connecting its atom
codes to `PaperTypes.Ty` or the original abstract `Sorts.Descriptor`; it has no
original endpoint allocation, source declaration, Return, event/root/scope
mapping, or `sameScoped` bridge. It establishes a useful graph lemma only.

The one-sided subtype-only candidate from R214 is rejected: a Value lower
bound alone permits `.top` at the readout variable. R220 avoids that local
countermodel with reciprocal bounds, but its structural definition is still
not evidence that the selected Yulang algorithm actually generates those
clauses at an original source literal.

## Equations the gate requires

1. **Independent generation.** Define the literal Value/Effect clauses from
   the original source occurrence and algorithm, without consulting source
   judgment, `Kernel.atom`, a candidate solver result, or a chosen typing.
   Pin the actual endpoint/coordinate relation. Establish that all eight raw
   payload forms retain their source identity in the same occurrence.
2. **Every-solution interpretation.** For any assignment satisfying exactly
   those generated clauses, derive a decoding into the original descriptor
   and effect carriers. Prove the base descriptor is the adopted literal
   type and the intrinsic performed effect is empty. No subtype bound is
   called equality without a separate derivation.
3. **Source row and witness.** Combine the syntax-fixed `v(l)` with the
   assignment-derived descriptor/effect at the same `q,r,e₀,ξ,ω`; preserve the
   shared witness and all enclosing source obligations. Do not substitute
   `finalRoot` for original `r`, or alias synthesis with `writtenTarget`.
4. **Parent use.** Consume the equation in the actual literal case of the
   unchanged parent proof. Any remaining constructor case stays present; the
   local result does not close the full universal theorem.

## Current disposition

The adopted L1 decision fixes source meaning but expressly leaves independent
generation, satisfaction, readout and Rust behavior open. The R213 model gate
requires a derivation-backed original-carrier equation before theorem-worker
activation. The frozen source audit is
`tasks/agent-loop/inbox/original-literal-realization-r231-source.md`,
SHA-256 `6d790a57ced06aa6274fd8da7b29e3276b854aa27577a468f0583ddc41334bd2`.

The actual native producer emits reciprocal Value bounds and
`bottom ≤ effect ≤ empty` for Unit, Boolean, Integer and String source forms.
DecodedString is an interpolation piece, not a fifth L1 literal constructor.
The inspected `LocalSourceForm` and literal producer have no FloatBits, Bytes,
Path or Character variants. Integer spelling-to-`Int` and String spelling-to-
raw-String payload decoding also remain unproved. These are native owner facts,
not the authoritative mathematical generator or a reason to narrow the eight-
form source domain.

The first missing equation is original source allocation/embedding from all
eight payload forms to the independent Value/Effect clauses at the original
ports. The second is every-solution decoding from those clauses into the
original descriptor/effect carriers, at the same source coordinate with the
syntax-fixed value, original root/event, scope, shared witness and pure Return.
The second gap remains even for Unit: native graph APIs report one completed
solver state and do not define arbitrary-assignment interpretation into
`Sorts.Descriptor`, `Sorts.Value`, `Sorts.Root` or `SourceAssignment`. Neither
R220's graph lemma nor `LiteralAtom` supplies that equation.

Therefore the model gate is **MODEL-INCOMPLETE**; proof activation is closed
and no theorem worker or Lean target is active. No parent premise is removed.

The source audit is not an independent semantic oracle and makes no
source-qualified counterexample claim. No source-domain restriction, new
literal rule, Rust change, Lean theorem, test, default build, cache output, or
parent delta is claimed in this note. Fresh conformance review must verify
this exact missing-equation disposition before the checkpoint closes.
