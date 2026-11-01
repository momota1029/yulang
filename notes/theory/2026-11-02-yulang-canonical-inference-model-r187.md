# R187 — canonical inference model attempt and exact denotation boundary

Status: **INCOMPLETE mathematical specification; frozen for independent review**.
Author: `/root/r187_canonical_model` (`researcher`). Baseline:
`41eb4bc24a82baa5ff203b48394041df76c848a7`. Governing packet: R187 revision 7,
SHA-256 `999213b617db69cc2511692b6338f4c814fe8768d119ba477749124ee07b6218`.
This is neither a complete model nor a theorem. No original parent premise is
closed or refuted. No semantic alternative is selected here.

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`):

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a.
```

The attempted construction starts with one scoped, whole-relation constraint
object. It reaches an explicit independent Call-denotation boundary before it
can supply that parent's concrete `generates` and `solves` instance. The
boundary is a missing construction in this artifact, not evidence that the
accepted language meaning is inconsistent or that a user must choose new
semantics. The complete accepted source domain remains 13 expressions,
11 patterns and 3 statements; none is declared unsupported.

## 1. A concrete representation prefix

Use distinct domains for resolved source sites, source Value identities,
type/effect variable identities, declaration occurrences and logical binder
occurrences. An identity in one domain does not supply an incidence in another.
Let a constraint object have the following finite representation:

```text
C = (Δ, Decl, N, root, RefValue, birth, Extrusions, History).
```

`Δ` is the original binder/dependency tree. `Decl` records each declaration's
sort, owning introduction and exact dependency telescope. `N` is a finite
registered graph of whole-tuple clauses, not separate port predicates. Its
syntax is:

```text
N ::= true | Primitive(δ, operands)
    | StructuralSubtype(kind, lower, upper)
    | And(N,N) | Or(tag,N,N)
    | Image(op, operands, result)
    | Scope(binder,N) | Rename(scopedMap,N) | Ref(root,scopedMap).
```

`Primitive` names an authentic independently specified local declaration at
its full operand telescope. It is not permission to add a desired source
judgment, arbitrary Function inclusion, admission-success Boolean or C0 law
as an opaque new primitive. Whether the required primitive/operator catalogue
has actually been supplied is a separate obligation below.

The structural terms are the pinned `SimpleSubConstraintSyntax.Term`: two
kinds, variable/atom, bottom/top, union/intersection, four-port Function,
record/tuple/variant constructors with their labels, order and optional bits.
For a structural valuation `ρ`, the already defined independent structural
relation is exactly

```text
ρ ⊨struct (l <: u)  ⇔  Sub(subst ρ l, subst ρ u).
```

This equation is not a denotation of complete source Function admission or
effects. In particular, an effect atom's numeric identity cannot replace its
original permission, operation-witness, scope and dependent relation fields.

The whole-relation connectives have ordinary shared-assignment meanings:

```text
η ⊨ And(P,Q)       ⇔ (η ⊨ P ∧ η ⊨ Q)
η ⊨ Or(tag,P,Q)    ⇔ the original tagged alternative holds on η
η ⊨ Rename(m,P)    ⇔ η∘m ⊨ P
η ⊨ Exists(b,P)    ⇔ ∃ z in the independent domain of b. η[b↦z] ⊨ P
η ⊨ Forall(b,P)    ⇔ ∀ z in that same domain. η[b↦z] ⊨ P.
```

The binder's domain is required to be independently defined; these equations
do not define that domain by source typing of the expression being proved.
Shared/OneShot binders retain one assignment at their original scope;
ViewLogic remains below its description dependencies and before its challenge;
actual events and EventProof remain beneath their original event telescope.
Registered recursion retains graph edges. Positive finite-derivation recursion
and the selected hereditary greatest fixed point are distinct interpretations,
not interchangeable readings of every recursive node.

These representation and connective equations follow the selected source
Generalize construction §§3.3–5.2 and source-contracts §2.1. They give an exact
place for complete local meanings; they do not manufacture those meanings.

## 2. Source App equation and the first unresolved interpretation

For an unannotated App at site `q`, a conservative symbolic generation attempt
allocates its actual ViewLogic declaration `v_q` at the source scope and emits
the following conjunction with the two child objects at that same scope:

```text
Gen(Γ, App_q(f,a)) = Exists(v_q,
    Gen(Γ,f) ∧ Gen(Γ,a)
  ∧ DescriptorFormation(q,f,a,v_q)
  ∧ WholeArgumentCompatibility(q,f,a,v_q)
  ∧ CompleteCallCertificate(q,f,a,v_q)
  ∧ SourceCallIncidence(q,f,a,v_q)
  ∧ CallableImage(q,f,a,v_q)
  ∧ CheckValue(returned(f), descriptor(q))
  ∧ CheckComputation(callableImage(q), synthesis(q))
  ∧ [RoleAndInitialCallOrigin(q,f,a,v_q) if singletonFormalCall(Γ,f,a)]).
```

The square-bracketed clause is present only under the actual source test in
`OriginalSourceGeneration.singletonFormalCall`: unannotated Name/Name,
one-use unannotated Value formal callee and Value formal argument. A written
annotation adds its actual final-formation clause and direct source boundary;
it does not overwrite the synthesis endpoint. This displayed equation is a
source-clause representation attempt, **not** a proof that the abstract
Simple-sub generator emits it or that a structural store solves its clauses.

To finish even this interpretation, the displayed Call clauses must expand
into an independently defined mathematical Call relation. The authenticated
authorities supply this structural equation, at one identical argument,
provider, event and world tuple:

```text
Call_struct(q, cf, carrier)
  = Bind_Y(cf, λ(returnedCallable,currentWorld,sharedWitness).
      ExecuteCallable_Y(actualProvider(returnedCallable),
                        carrier,currentWorld,sharedWitness)).

Call_complete(q, cf, carrier)
  = the original complete operation Q_q,
    retaining Call_struct and every authentic complete declared alternative.
```

`ExecuteCallable_Y` includes the real entry/role, receipt, designated consumer,
body, invocation return and pending developments. Value entry performs the
designated Force and actual Return/rebind; retained Computation entry retains
the carrier. Callee-pending and receiver-pending suffixes remain distinct and
receipt is not replayed. Bind has the supplied Return/Request equations:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C, λ(response,C'). k(response,C') >>= S).
```

Those equations determine part of the operator structure. The following
required defining expressions are **unexpanded in this artifact**:

```text
⟦independent complete Call domain at (q,η,Δ)⟧ = ?
⟦Call phase / current-world binding / receipt admission at (q,η,Δ)⟧ = ?
⟦complete observation interface of Q_q at that same tuple⟧ = ?
```

Consequently the intended denotation of
`CompleteCallCertificate(q,f,a,v_q)` is not yet defined independently of the
source-side local rule or of a supplied complete-typing fact. This is the
first stopped defining equation. Writing `C0_q` on the right of it would
preserve an explicit premise, rather than construct the requested denotation.
Writing `Satisfies(Build(App_q(f,a)))` there would only reuse the source-side
target. Neither is used here to finish the model.

The selected contextual Function meaning does give the required *shape*:
every independently admitted complete checked challenge must be accepted by
every genuine actual provider decomposition of the same callable, and every
actual complete or pending observation must meet the descriptor's whole
observation interface and hard envelope. Its own §2 explicitly retains the
independent context domain and complete admission/observation relations as
inputs. `OriginalSourceInterpretation.Inputs:324–372` exposes those inputs;
the greatest-fixed-point definition of `Meaning` does not fill them.

The required missing construction is therefore the independent local
operator/domain/observation equations and their same-tuple correspondence to
these generated App clauses. It is not another four-port variance lemma and
not a claim that a Function interpretation must depend on four scalar ports
alone. The proposed `C` retains the entire scoped graph precisely so those
equations can use all original joint information.

## 3. What the newly admitted C0/IF authorities actually settle

| Authority and exact section | Established definition supplied | Explicit remaining input |
| --- | --- | --- |
| complete-Call definition §2 | Authentic reference to the original complete operation; structural callee Bind followed by execution of the actual returned receiver; original abstract alternatives retained | Independent complete C0; no concrete W/Z grammar is supplied |
| complete-Call definition §5 | Exact captured Call indices and `A-UpperCallRef` constructor, preserving authentic `Q_q`, `SpecCall_q` and the same full IF graph | The constructor takes `C0_q`; it does not prove it |
| source-interface definition §§1–3 | IF-Insert/IF-Use and complete contextual slots, carrier hole, dependent receiver/current-world and output/future incidences | Original operator typing, witness actions, actual dispatch/phase validity and contextual hole/world binding |
| source-interface definition §4 | Source-interface formation is constructed on its stated envelope | Primitive validity, complete C0, other source forms and all-source adequacy remain separate |
| native signature definition §§1–2 and selected incidence construction §§2–6 | Full typed catalogues, original provenance partitions, separate receiver placement, declared/reference/upper/annotation formation and whole-family actions | Actual independently typed primitive/operator laws; symbolic support does not prove an inhabited licensed fibre |

IF constructs contextual incidence. C0 is a semantic typing requirement on the
unchanged full interface. Neither implies the other merely because its record
contains the same endpoints. These definitions permit a future independent
operator construction to be used here without reconstructing ownership from
IDs. They do not supply that construction in this artifact.

The source-contracts §3.7 production abstraction leaves concrete W/Z relations
unselected. That fact is **not** used as the obstruction to this mathematical
source-model packet. Its finite algebra illustration is not a Yulang source
counterexample, and no production or Rust correspondence claim is made.

## 4. Selected phase equations that the eventual model must preserve

The exact stopped Call denotation prevents a complete whole-language transition
definition. The following equations record the determined structural and
scope parts, without asserting that their missing local relation actions have
been supplied.

1. **Accumulation.** Add the actual generated comparison/clause to the one
   shared store; retain the original whole relation, declaration and scope.
   It is not a generation-time satisfiability test. Opposite lower/upper bounds
   of one variable generate their actual replayed comparison. Four-port
   Function comparison has variance `(-,-,+,+)`.
2. **Extrusion.** At target level `l`, acceptable variables and primitive
   terms remain unchanged. A wrong-level variable `α` allocates its actual
   polar copy `copy(α,p,l)` and memo entry before traversing bounds. Positive
   extrusion adds `α <: copy` and copies selected lower bounds; negative adds
   `copy <: α` and copies selected upper bounds. Function arguments and
   argument effects flip polarity; results and result effects preserve it.
   Retain the actual occurrence identity, source-origin Value, receiver Value
   and every produced polar parent/copy pair. Fresh use alone is not extrusion.
3. **Current intrusion qualification.** For each immutable source Value birth
   level `k`, use `V_k={v | birth(v)=k}` and
   `Ref_k=RefValue∩(V_k×V_k)`. A recorded extrusion occurrence qualifies only
   when its origin and receiver lie in one SCC of this induced graph. Paths
   through other birth levels do not qualify it. This replaces the older
   cross-level qualification; it does not delete cross-level source edges.
4. **Intrusion update.** For the qualifying occurrence, add equality of its
   actual retained parent/copy pairs, preserve accumulated clauses, and replay
   consequences through their real consumers. If represented by a quotient,
   apply the same map to every incident constraint/declaration field and retain
   all original clauses. A type-coordinate quotient never changes Value birth.
5. **Generalization.** At the actual publication `(p,component)`, retain the
   final formed source root and full component relation. Traverse fixed
   Established/OneShot/Intrinsic dependencies and retain original Shared
   binders; internal own-component relation edges remain internal. Exactly
   reachable ordinary owned Desc declarations outside the fixed closure become
   templates at their original scopes. New independent uses allocate whole
   description frames; aliases share a frame. ViewLogic/Event/EventProof and
   runtime fields follow their different source allocation rules. A numerical
   level threshold alone is not a substitute for this scoped eligibility rule.

For the structural subproblem, a terminal assignment pulls back through a
renaming by `ρ_before(k,i)=ρ_after(k,q(k,i))`. At an extrusion cut, the retained
links prove the one-sided approximation needed to reflect the rewritten demand
to the original demand. The §4 diagonal lift instead starts with a solution of
the **original unextruded demand** and assigns each fresh copy its parent's
value; that is a different direction and keeps that antecedent.

The complete transport required here would be

```text
η_terminal ⊨ N_terminal
  ⇒ η_original ⊨ N_generated
```

on the same original telescope, fixed fields, shared witnesses, event strategies
and complete Call/effect relations. The structural pullback and diagonal lift
do not prove this whole statement. No proof for the missing Call phase/world/
admission interpretation is inferred from them. Generalization's source
allocation relation is not silently identified with the solver's transitions.

## 5. Outcome and discriminating failure conditions

This packet reaches neither success outcome in the R187 contract. It is not
outcome A: no complete independent denotation, complete generator/solver
instance, all-constructor theorem or reviewed correspondence is present. It
is not established outcome B: there is no proof that the original authorities
permit observably different language meanings, no source-qualified generated
constraint counterexample and no semantic impossibility result. An existing
selected operation is repeatedly referenced, so absence of its expansion here
must not be reported as global semantic underdetermination.

The construction would fail review if any of the following were used to fill
the stopped equation: treating support as a license, assuming C0, assuming the
desired App admission, replacing whole relations by port projections, choosing
a different satisfying assignment for a child, or defining solving as source
`Build` satisfaction. The current artifact makes none of those substitutions.

No oracle, executable experiment, random seed, bounded search or mutation was
used. There is no finite-model experiment offered as evidence about actual
Yulang generation. The only checks were input SHA-256 authentication and
bounded source reads. No Lean/build/test/Rust/Cargo/environment/cache/scratch
operation ran.

The named prerequisite “actual generation represented by one canonical
independent constraint object” remains **OPEN**. Soundness, source coverage,
principality and combined termination remain **OPEN**; native/Rust
correspondence remains later and separate. Original premises removed: **0**.

Recommended next action: construct or recover the independent mathematical
Call operator/domain/observation equations for the original source, at this
same full tuple and telescope, and apply them to the displayed generation
equation. Do that before admitting another soundness induction or conditional
App lemma. The primary must choose the exact source packet and pins; this
artifact grants no further reads or new semantic decisions.
