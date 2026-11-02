# Canonical literal generation: reviewed algorithm proposal

Status: **Research proposal; not Authoritative; no algorithm adoption or
implementation authority**
Parent target: `YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`
Prepared under R237, baseline `ed75110c7816f2e8be7adb6ca02cd949222f2a3a`

## Purpose and decision boundary

This proposal joins the adopted original literal rule to a possible
Simple-sub generator equation and writes the literal case that would be needed
in the unchanged soundness proof. It keeps three claims separate:

1. **Adopted source fact:** L1 fixes each raw literal's complete payload,
   `Value(τ(l))`, literal value `v(l)`, empty intrinsic effect, pure Return,
   and original coordinates `(q,r,e₀,ξ,ω)`.
2. **Candidate generator equation:** a source-directed generator can emit the
   corresponding canonical type/value constants without first allocating a
   type variable to be solved to those constants. R236 checks the payload map
   and symbolic `Build` input. The exact all-eight algorithm equation is not
   yet authorized.
3. **Open arbitrary-solution bridge:** from the actual generated constraint
   problem and any satisfying assignment, construct the original local source
   judgment and `sameScoped` witness. Neither L1 nor R236 supplies this.

This document is a proposal for independent authority review. It does not
change L1, define the `SourceProblem` instance, or promote any source form or
proof gate.

## Source equations already fixed

For each original raw literal `l`, let `p(l)` retain the entire payload,
`τ(l) = PaperTypes.literalType(p(l))`, and
`v(l) = PaperTypes.Value.literal(p(l))`. The adopted local row is:

```text
LitRow(q,l,r,e₀) =
  ⟨ descriptor = Value(τ(l)), value = v(l), root = r, event = e₀ ⟩

Return(LitRow(q,l,r,e₀)) =
  ⟨ Comp(empty, τ(l)), v(l), r, e₀ ⟩
```

The scope `ξ` and shared witness `ω` stay those of the enclosing derivation.
The source rule creates no root, event, occurrence, scope or witness. Its
intrinsic empty effect does not erase contextual permission, actual inflow,
residual effects, Call effects, guards, futures or conversion obligations.
All admitted checking/conversion alternatives retain their own premises,
ports and effects. In particular, do not equate the synthesis descriptor,
written target and `finalRoot` merely because an ordinary unannotated literal
uses the base introduction.

Authority: `notes/design/2026-11-02-literal-l1-adoption.md` fixes these source
facts and explicitly withholds the Simple-sub generator clause, satisfaction,
solver readout and `sameScoped` interpretation.

## Proposed algorithm equation (not adopted)

One candidate realization of those source facts is a direct constructor:

```text
generateLiteral(q,l,ξ; r,e₀,ω) =
  ⟨ source = (q,l),
    synthesis = Value(τ(l)),
    value = v(l),
    intrinsicEffect = empty,
    return = Comp(empty,τ(l)),
    root = r, event = e₀, scope = ξ, witness = ω ⟩
```

The candidate generator consumes the original payload-bearing literal node
emitted by the original symbolic `Build` relation. It emits canonical
constants directly; it does not consult a chosen typing, solver result,
`Kernel.atom`, or source judgment to choose the type. R236 proves the
payload-preserving map for unit, bool, int, floatBits, string, bytes, path and
character; the L1 type/value table; preservation of supplied coordinates; and
the connection to R196's exact symbolic `Build` literal atom. R236 does not
prove this proposed equation is the selected Yulang algorithm.

For the actual inference relation, the owner must choose and specify a
constraint-level result whose denotation validates this row for every
satisfying assignment. The direct-constant equation above is one concrete
proposal, not a theorem about an unspecified `generates` or `solves`. If
another representation is selected, it must still derive the same source row
and Return without using source typing or a successful solver run as its
definition. Inference must remain generation followed by accumulation,
propagation, level-aware extrusion/intrusion and generalization; it must not
special-solve a constraint while generating it.

## Exact proposed soundness use

The unchanged root is:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

At the source literal constructor, the induction step must establish that
the **same** generated problem `d` and **arbitrary** satisfying assignment
`a` induce the original local L1 premise at the same occurrence and scope:

```text
sourceLiteral = l at (q, ξ)
generateLiteral(s,x,q,l,ξ) contributes clauses to d
solves(d,a)
  ⇒ the row read from the original assignment is LitRow(q,l,r,e₀)
     and its Return is Comp(empty,τ(l)) with value v(l)
     under the same (q,r,e₀,ξ,ω)
```

The conclusion needed for the constructor is the original literal rule
instance inside the full `sourceJudgment`, followed by the original shared
`sameScoped s x e a` witness. The local statement cannot choose a new `r`,
event, scope, witness, root, or assignment; it cannot replace the root with an
unrelated `finalRoot` read. The enclosing induction must retain all other
source premises and original checking alternatives.

This is a proof obligation template, not a theorem. Present Lean definitions
do not yet give `generates` and `solves` an independent full Yulang literal
interpretation. `OriginalSourceGeneration.Build` compiles original source
rules whose leaf meanings still come from `Kernel`; it is not by itself
Simple-sub generation. `OriginalSourceInterpretation.SourceAssignment.row`
currently reads `.finalRoot`, and `LiteralAtom` assumes a declaration,
groundness and its carrier inputs. None of these facts follows from arbitrary
Simple-sub satisfaction in R236.

## Authority review

The source review must decide whether the candidate direct equation is already
entailed by existing authority or selects a new algorithm decision:

- The top-level principles §1 and §1.1 require ordinary source type/constraint
  construction before propagation, prohibit special solving during
  generation, and use symbolic endpoints for unknown types. They do not name
  the all-eight equation above.
- The pinned Simple-sub reference's literal branch (`Typer.scala:73–74`)
  directly returns the canonical type for integer literals. That supports the
  integer case, not the other seven Yulang payload forms or effect/Return
  carriers.
- Typed-core elaboration §6 lists literal synthesis as `Value(type of literal)`
  but is draft material without implementation authority. Its table supports
  the source-level shape, not an adopted Simple-sub generator equation.
- The 2026-10-04 source-generated callback/structural package is a reviewed
  conditional theorem package with no implementation authority. Its
  theorem-scoped pure structural shadow cannot decide the full effectful
  Simple-sub model.
- L1 is authoritative for the source row only and expressly excludes the
  generator decision.

Therefore the review cannot promote the equation merely from matching the
source table or from R236's Lean checks. If the reviewer finds no existing
algorithm authority for all eight direct constructors, request a narrow user
decision on this exact equation before adoption or theorem activation. Keep
R236 as a checked candidate meanwhile.

## Falsifiers and review seam

Reject this candidate as stated if any actual source rule:

- requires a different source introduction or loses an independently
  admitted checking/conversion alternative;
- merges synthesis, written-target and final-root ports;
- substitutes the literal's root, event, occurrence, scope or shared witness;
- resets contextual effects or drops enclosing Call/effect/guard/future
  obligations; or
- defines generation by an already chosen typing, successful solving or
  original `Kernel` source judgment.

Review the frozen authority classification, all eight payload mappings,
constraint denotation for arbitrary satisfying assignments, exact original
`Build` consumer and literal induction obligation. A green Lean build of R236
does not decide the algorithm-authority question. A successful adoption would
authorize only the generation equation; it would not prove soundness, source
coverage, principality, termination, Rust correspondence or production
readiness.

## Exact remaining premises and accounting

1. Existing algorithm authority or explicit user adoption for the proposed
   all-eight direct generation equation.
2. An independent mathematical constraint semantics and actual constraint
   generation/solve relation.
3. A theorem from every satisfying assignment to the original descriptor,
   payload value, root and event at the correct source endpoint; include
   intrinsic effect and pure Return without conflating contextual effects.
4. The same-scope, same-witness literal induction application inside the
   complete unchanged `InferenceSoundness` root.
5. Separate Call/effect admission, checking/conversion, and every other source
   constructor; these are not discharged by a literal case.

Parent-premise delta at proposal time: **0**. Closed roots: **0/4**. No Rust or
production change is proposed. The implementation lane remains
`NO_SAFE_CODE_SLICE`: the candidate source producer and runtime literal decoder
do not define the arbitrary-assignment theorem above.
