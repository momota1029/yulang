# Adopted literal L1 independent equation — R214

Status: **REVIEW_PENDING; MODEL-INCOMPLETE**. Parent roots are unchanged; R213 left **0/4 roots** and
**0/5 packages** closed.

## Target equation

For each original literal `l` at `(q,r,e₀,ξ,ω)`, the adopted source rule fixes
`Value(τ(l))`, the raw literal value `v(l)`, and
`Return = Comp(empty,τ(l))`, preserving the original root, event, scope,
occurrence and shared witness. The eight constructors and payloads are fixed by
the L1 adoption. This work must establish that independently generated
Simple-sub constraints and one arbitrary satisfying assignment yield the type/effect premises
needed by that source rule, rather than assuming the source
`LiteralDeclaration` or a chosen readout. The raw runtime value is fixed by the
original literal syntax; it need not be encoded as a type term.

## Candidate representation under audit

The existing Simple-sub algebra has separate Value and Effect kinds and
structural terms, but its opaque atoms are `Nat` identities. The concrete
`LatticeInference.StoreSatisfied` relation decodes store clauses to graph node
pairs and checks the lattice `RegularSub` relation. A successful subtype
comparison is not by itself exact node equality. `OriginalSource.SourceAssignment` separately
contains endpoint-indexed descriptor, value and root functions plus one event.
The L1 authority names `PaperTypes.Ty` and `PaperTypes.Value`, while the original
interpretation's `Sorts.Descriptor`, `Sorts.Value` and `Sorts.Root` are abstract
and are not identified with those paper carriers.

A proposed ground encoding therefore needs an explicit map for the eight base
types, separate Value/Effect coordinates, and a same-assignment decoding
relation to the original descriptor/effect sorts. The literal payload is not a
field of `SimpleSub.Term`; the source witness can take `v(l)` from the original
literal constructor. `sameScoped` must combine that syntax-fixed value with the
descriptor/effect facts obtained from the satisfying assignment. Current
`Contracts.SourceProblem` leaves that relation abstract.

## Equations to establish or reject

1. **Generation:** from raw source literal `l` and occurrence/scope, form
   actual Value and Effect constraints without consulting source judgment,
   source `Kernel`, or solver output.
2. **Satisfaction:** one regular graph assignment satisfies those clauses;
   the definition must say whether the clauses constrain exact ground shape or
   only subtype bounds.
3. **Readout:** that same assignment supplies the L1 descriptor/effect facts;
   the source literal supplies `v(l)`. Their joint source witness retains
   `(q,r,e₀,ξ,ω)` and the pure Return.
4. **Context:** annotation keeps `synthesis` separate from `writtenTarget`; all
   checking/conversion alternatives and enclosing permission, inflow, residual
   and future obligations remain present.

A `RegularSub` bound alone cannot be called an equality. In particular, any
candidate that permits a non-ground supertype without an admissible source
subsumption rule, or selects the final root in place of original `r`, fails
the target equation. The payload identity is fixed by the source constructor. The
model must demonstrate that the actual constraint form rules these cases out,
or record the exact missing authority/equation.

## Known boundary

`CanonicalSourceInferenceModelR196.literal_generated_formula` proves only the
existing source `Build` equation for every raw payload. It does not produce
independent constraints or bridge their solutions to `LiteralDeclaration`.
`OriginalSourceInterpretation.LiteralAtom` still accepts a supplied declaration
relation and checks groundness; it does not provide the Simple-sub implication.
The L1 adoption intentionally leaves generation, satisfaction and readout
open. These facts are not evidence of impossibility or a need for a new literal
semantic decision.

No source constructor is dropped. The selected source Return law has empty
intrinsic performed effect; contextual effects are retained separately. No
Rust meaning, theorem closure or successful solver execution follows from this
model construction.

## Concrete test of the weakest subtype-only candidate

Suppose a literal's generated Value clause only says
`atom(typeCode (τ(l))) ≤ var(q)`, and readout interprets the variable by its
upper graph node. This candidate fails for every literal: form a graph with an
`.atom (typeCode (τ(l)))` node and a `.top` Value node, and assign `q` to the
latter. The decoded comparison expands to `some []` because the upper node is
`.top`; the lattice `top` rule followed by `regular_fold` proves
`RegularSub`. Thus the store is satisfied
while the readout is `.top`, not the adopted exact base descriptor. This is a
falsifier of the one-sided candidate, not of every possible generator. Adding a
reverse bound or using a source subsumption rule changes the proposed equation
and requires its own exact readout argument.

The payload is a separate coordinate. `SimpleSub.Term` and the lattice graph
nodes carry type/effect shape and opaque atom IDs, not a `PaperTypes.Value`.
That does not by itself block soundness: the source witness can obtain the raw
value from the original literal constructor. The required noncircular equation
must say how that syntax-fixed value and the original `(q,r,e₀,ξ,ω)` coexist
with the descriptor/effect facts obtained from the same satisfying assignment
in `sameScoped`. Current `SourceProblem.solves` and `sameScoped` are abstract,
so the source/type split has not yet been defined.

Therefore the first still-open equation is concrete and localized: define the
source-independent Value/Effect store clauses and their relation to the
original descriptor/effect coordinates, then show those facts instantiate
the adopted source literal rule. If the satisfying graph yields a supertype,
the original source rule must admit it; exact identity cannot be assumed from
one-sided subtyping. The source value comes from the original literal syntax,
and `sameScoped` must retain it alongside the assignment-derived type/effect
facts. Existing
L1 fixes the source row; `SimpleSubConstraintSyntax` fixes the constraint
algebra; `OriginalSourceInterpretation` leaves both `Sorts` and
`LiteralDeclaration` abstract. None of the pinned authorities defines this
bridge. This is an authority/model-construction gap, not a counterexample to
L1 or evidence that new source semantics are needed. No parent premise moves.


## R214 checkpoint status

This freezes the candidate audit and its exact open equation for independent
review. The one-sided subtype-only candidate is refuted by the top-node model;
that does not refute a two-sided or source-subsumption construction. No complete
source-indexed generator/readout equation is defined by the pinned authorities,
so the L1 parent premise remains open and no theorem is admitted. Parent delta
remains **0/4 roots; 0/5 packages**. This is a review-pending model checkpoint,
not an accepted outcome.

## Pinned evidence and claim class

Research-only source pins against baseline `yulang3/9bf70ea58`:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- L1 adoption: `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`
- `OriginalSourceSyntax.lean`: `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceInterpretation.lean`: `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `SimpleSubConstraintSyntax.lean`: `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- `SimpleSubRegularSolutions.lean`: `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`
- `SimpleSubLatticeInference.lean`: `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- `SimpleSubLatticeCertificates.lean`: `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`
- `PaperExecutionSyntax.lean`: `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d`
- reviewed R213 model: `17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e`

Claim class: exploratory research checkpoint, independent review pending. This
document does not claim a theorem, complete equation, closed parent, production
conformance, or semantic authority. Its concrete result is limited to
refuting the one-sided lower-bound candidate and identifying the precise
source/model bridge still required.
