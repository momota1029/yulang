# R232 original literal equations — construction record

Status: construction in progress; no theorem or source semantics changed.
Parent: `YulangClosure.SourceProblem.InferenceSoundness`, unchanged at
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`.
Baseline: `05586b1473e3194b80fb5ce7b30c531875e27929`.

## Evidence fixed before this construction

The adopted L1 source rule supplies the complete raw payload map, intrinsic
type/value, pure Return, original root/event/scope/shared witness, and the
requirement to retain contextual effects and checking alternatives. It does
not define a Simple-sub encoding or solver readout.

`OriginalSourceGeneration.sourceRules` currently maps a literal at lines 85–89
to a `.lit` rule with one `.literalDeclaration` atom carrying the exact
`Literal`; it allocates no `SimpleSub` value/effect coordinate. `Build` compiles
this source-rule tree and `Satisfies` delegates local meaning to
`OriginalSource.Kernel`. This is source-rule generation, not independent
Simple-sub constraint generation.

`SimpleSub.Term` has `var Nat`, `atom Nat`, `bottom`, `top`, structural
constructors and unions/intersections. `Constraint.Satisfied` uses its
structural `Sub` relation. The current syntax has no named Unit/Bool/Int/Float/
String/Bytes/Path/Char base-type constructors, no typed source coordinate map,
and no direct interpretation from a valuation into `OriginalSource.Endpoint`
descriptor/value/root/event fields.

`OriginalSourceInterpretation.SourceAssignment` is endpoint-indexed, but its
fields are supplied independently. `LiteralAtom` assumes the declaration,
ground descriptor and groundness predicates. It reads `.finalRoot`; this does
not establish the distinct synthesis/writtenTarget/finalRoot relations for an
annotated literal. These definitions cannot serve as the missing arbitrary-
solution construction.

## Equation attempt at the fixed model boundary

For a raw literal `l` at `(q,r,e₀,ξ,ω)`, an independent generation clause
would need to return (i) fresh value/effect coordinates at the original
intrinsic ports and (ii) the actual source-indexed `SimpleSub.Constraint` store.
The natural structural shape to investigate is

```text
VarValue(α) ≤ Base(τ(l))    Base(τ(l)) ≤ VarValue(α)
BottomEffect ≤ VarEffect(ε) VarEffect(ε) ≤ EmptyEffect
```

with `τ` and `v` taken from the approved eight-form L1 table and the complete
payload preserved. This is currently a candidate shape, not an equation: the
abstract authority has not yet been located in the existing Lean types for
`Base`, `EmptyEffect`, fresh allocation, or the source-port interpretation.
The existing abstract `atom Nat` cannot be assigned those roles without
specifying typed identities, collision behavior and their relation to the
original semantic carriers.

Even if this store equation were fixed, its satisfaction only yields
`Sub`-facts on substituted `Term`s. A missing lemma must interpret the
reciprocal base bounds as equality at the original descriptor and interpret
the effect bounds as the original empty effect. A second missing construction
must turn an arbitrary satisfying valuation into one coherent original row:

```text
descriptor = Value(τ(l)); value = v(l); root = r; event = e₀
Return = Comp(empty,τ(l)); scope = ξ; shared witness = ω.
```

The literal payload fixes `v(l)` in the source rule, while the generated
constraints have no value-language constructor. Thus source-value readout
must be supplied by an approved syntax-to-original-value embedding and
retained at the same source occurrence; it cannot be inferred from equality
of type atoms or native constructor tags.

## Current decisive boundary

The existing evidence does not determine the `Base`/`EmptyEffect` embedding,
fresh typed coordinate allocation, or valuation-to-original-carrier map. These
are definitions needed to state and derive the candidate equations, not
conclusions that follow from R220 structural graph lookup or from the four
native literal families. No honest derivation can currently construct the
parent's literal premise from an arbitrary `ρ` without supplying these maps.

The next allowed action inside this contract is to trace the adopted Simple-sub
algorithm and selected mathematical authorities for these exact definitions.
If absent, freeze the smallest typed interface and its authoritative owner,
then stop `MODEL-INCOMPLETE`; do not make it a hypothesis of a downstream
theorem. Parent-premise delta remains 0.
