# Hole elimination, observations, and interval facets

Status: **Partial proof; the source-to-elimination bridge remains open.**
Date: 2026-11-13. Base: `f71f1d626030f9557aa42df5bdc346d13bf02fae`,
branch `astra/hole-elimination`.

Authority: spec/06-roles.md §6, B4 addendum 7, and the current task. This refines
§4 of [Shared origins and lazy nonpoint readback](2026-11-13-nonpoint-provenance.md).
It makes no new language decision.

## 1. Two distinctions needed before counting holes

An observation update is not necessarily a semantic assignment. In particular,
revealing a head already implied by the ordinary constraints need not eliminate
an unknown variable. Counting every refresh as one acyclic substitution is wrong.
The existing administrative accessibility proof already counts this progress by
observation facts. Such updates should preserve the hole representation and use
that separate measure.

There are also two different kinds of provenance:

- An **actual input origin** denotes the shared actual argument, potentially a
  nominal argument inside a strict interval. The existing `Origin` and `Same`
  relation retain that identity.
- An **interval facet** denotes a lower or upper bound. Repeated captures compute
  the join of their lowers and the meet of their uppers. These are ordinary finite
  lattice expressions; they are not generally equal to the actual argument.

`OriginTerms.Expr` represents constructor trees with actual-origin leaves. It
does not contain joins or meets, so it cannot serve as the only syntax for all
newly allocated endpoint IDs. Substituting an actual argument for a bound would
change the constraint semantics. The additive `HoleFacets.Facet` syntax repairs
this part of the proof representation without changing Step or its guards.

These are implementation/proof-interface gaps, not evidence of a semantic
termination gap. No new source-formed infinite shared-Step execution was found,
and there is no owner question from this analysis. In particular, forbidding a
legitimate recursive-source refresh would be an unjustified repair.

## 2. A concrete source-formed observation update

`GeneralNominalHoleObservation` reuses the one-slot source equation

```
x = { 7 : x }
```

from `GeneralSourceStateExamples.loopState`, including its inhabited regular
model. The role registry is empty and checked. The root has one point input
`(x,x)`. Before the update its separate normalized observation is unresolved;
afterward it records the one-field record and its self-edge. The ordinary source
equation is present throughout.

The new module proves `InitialSource`, an actual `GeneralNominalSharedSteps.Step`,
source formation after that Step, newly `Known` input, the structural self-edge,
and `CycleK2.RecursAt`. It also proves Acc from this initial state: more generally,
every source-formed shared-Step state with an empty registry is accessible.
Thus this example is expressly not a termination counterexample.

Both the opaque readback `leaf x` and the exposed readback `record[7](leaf x)`
are valid over the original basis `[x]`. `exposed_readback` derives the latter
from the actual source model equation and structural projection law.
`not_elimination` says that this literal exposed expression still contains x;
it is not an expression over the empty remaining-hole set. This theorem does
not quantify over all possible semantically equivalent expressions. Its purpose
is to prevent charging the producer's actual observation as an acyclic hole
elimination. The opaque cyclic leaf is retained, and K2 governs its inspection.

## 3. The complete merge-endpoint producer

For a head variable a with captured intervals
`[(l₁,u₁), …, (lₖ,uₖ)]`, the actual allocation producer computes:

- k=1: reuse the two existing endpoints;
- k≠1: allocate the lower/upper IDs and record the equations to
  `lower = l₁ ∨ … ∨ lₖ` and `upper = u₁ ∧ … ∧ uₖ`;
- k=0: these expressions are bottom and top respectively.

`HoleFacets.capture_endpoints` proves both equations for **every multiplicity**
from the actual `Allocation.merges` constraints. It does not take the desired
endpoint equations as assumptions. `packet_endpoints` obtains those constraints
from `PacketSupport.Inputs`. `endpoint_leaves` proves that the leaves of these
computed expressions are exactly the old lower/upper endpoint lists: the new
numeric IDs do not become new atomic holes.

The same distinction survives materialization. `HoleMaterialization.endpoint_use`
uses the actual schema's `VariableHolds` definition. A lower-mode occurrence
reads the merged lower; an upper-mode occurrence reads the merged upper.
`packet_lower` and `packet_upper` supply the corresponding finite facet readbacks
for all declared input-variable occurrences in `inputSchema`. They use input
facts only, without the packet's outputs or cached context. `source_exact` handles
an allocated root ID; `compose` substitutes earlier facet representations over
a fixed basis. This closes the repeated-capture endpoint producer and its
lower/upper variable consumers, not the entire mixed constructor/facet grammar.

For intuition, a repeated head capture with intervals `[int,any]` and `[str,any]`
has lower `int | str` and upper `any`. A structural child argument `V a` is
materialized with those lower and upper facets. Its V head may be known while
its lower payload is still a join. The actual shared a can be any in a model;
replacing that lower payload by a would lose the distinction. This illustration
is not a newly formalized complete P/R installation trace or a nontermination
witness.

## 4. Composing readbacks without new leaves

`HoleReadback.Over M H r t` states both uniform observational readback of t at
origin r in every M-model and syntactic containment of all leaves in H.
`holds_bind` and `compose` prove substitution of earlier origin readbacks;
`alias` transports through actual-origin equality, and `project_readback`
extracts an already represented constructor child. None chooses a value inside
an interval or creates a fresh leaf.

`promoted_over_basis` combines this with the existing settled-output theorem.
Its exact remaining premise is a representation over H for each origin in the
trusted history's `inputOrigins facts`. That premise is not derived from
InitialSource here. It is the place where a global origin-producer invariant is
needed, rather than treating every newly encountered projection as a new hole.

`step_preserves` and `trace_preserves` retain existing readbacks by model
restriction under the actual shared Step. `refresh_exact` and
`reobservation_exact` prove equivalence with the **same term and same basis**
across those administrative operations. Preserving an old readback is weaker
than producing a new readback for every newly exposed observation.

## 5. The conditional calculation, now formalized

An elimination inventory consists of a finite list of remaining holes, a finite
list of symbolic terms, and a common depth bound. A genuine elimination chooses
a present hole h, represents its replacement using only the other remaining
holes, removes h, and substitutes the replacement consistently in every term.
The replacement has depth at most `growth N` when the old bound is N.

`HoleElimination.Trace` is this syntactic relation. It is **not** a new language
Step or a proposed definition of source formation. Starting inventories have
distinct holes. Replacement closure and bounded substitution are proved from
the computed replacement function. Induction gives

```
number of eliminations + remaining holes = initial holes
N₀ = initial depth
Nᵢ₊₁ = Nᵢ + growth(Nᵢ).
```

The iterate is increasing in its iteration count because each increment is
nonnegative; monotonicity of `growth` is not needed for that fact. Consequently,
`conditional_budget` proves at most |H| eliminations, depth at most N_|H|, and
membership of every final term in the **one finite enumeration over the initial
H, fixed constructor tests, and N_|H|**. This strengthens mere finiteness of the
final inventory. It still requires an actual elimination Trace as its premise.

The proposed connection to Paterson remains conditional as follows. Suppose a
finite symbolic representation of the eligible inputs has total size at most S,
and source-to-capture readback makes every generated unnamed child an instance
of the checked Paterson comparison. Keep this representation/substitution fixed
within a phase containing no semantic hole refinement; account separately for
updates that change it. Along a dictionary branch its size strictly
decreases, so there are at most S child edges. Let B bound declaration branching
and A bound associated-expression size, including variable multiplicities. A
coarse settled-output bound can be defined by

```
T₀(S) = A(S+1)
Tᵢ₊₁(S) = A(S+1+B Tᵢ(S));   F(S) = T_S(S).
```

The constant can be enlarged to cover all finite declaration overhead. Each
template substitutes input subterms of size at most S and at most B child
readbacks; its A occurrence bound controls duplication. This gives the displayed
recurrence. Replacing one hole in a size-N term by a size-F term gives a bound
such as N(1+F). Alternatively a finite test list and depth enumeration yield a
finite maximum input size S for the depth-based calculation above.

Neither the concrete Paterson/readback correspondence nor the settled-tree F
bound is established by the new Lean modules. `growth` is explicit in the formal
theorem. In particular, a known outer head is not itself a bound on the whole
eligible input structure.

## 6. Exact remaining source obligations

The following are still needed before applying that calculation to the shared
Step or constructing its `SignatureCover`:

1. Construct a finite initial origin frontier H, distinguishing opaque recursive
   source components from eliminable unknowns. Source IDs alone do not name the
   actual parameters of strict nominal intervals. Finiteness of all simple
   relevant projection paths and the K2 cutoff must be proved on this carrier.
2. Combine actual-origin constructor terms and algebraic endpoint facets in a
   complete representation for all head-relevant materialization. The local
   producers above cover their respective cases, not this combined invariant.
3. Show every new relevant origin/ID either has a representation over that H or
   cannot contribute to a head explanation. This includes output binders,
   materialized roots, alias transport and unused reservations. Existing settled
   guards exclude unfinished output facts; a complete free-ID/projection
   nonjustification theorem is not supplied here.
4. Extract genuine eliminations from semantic constraint progress while treating
   normalization, certified refresh and reobservation as observation progress.
   A projection crossing an opaque leaf must be justified without silently
   introducing another atomic hole. Not every nonempty update consumes H.
5. Derive the checked Paterson instantiation bound and settled-output growth
   function. Then derive the finite invocation/allocation/support bound and
   complete report enumeration. The existing SignatureCover retains exact
   occurrence and child identities; finite symbolic syntax alone is insufficient.

Thus the strongest general shared-Step termination theorem remains
`SharedBudget.accessible_of_signature_cover`, with its explicit cover premise.
`SourceBudget` and unconditional Acc from Checked + InitialSource remain open.
This change repairs concrete provenance sub-producers and formalizes the
conditional numeric calculation; it does not claim completion of B4(1).

## 7. Validation

The `yulang-proofs` workflow was used. The configured prover role and its launch
configuration were unavailable; no prover agent ran. The primary constructed
the proofs, and a separate read-only reviewer checked the counterexample search,
producer ownership, strengthened budget, and theorem scope. No blocking finding
remained in the reviewed changes.

Final commands from `lean/`, each with exit code **0**:

```sh
lake build Yulang.GeneralNominalHoleReadback Yulang.GeneralNominalHoleObservation Yulang.GeneralNominalHoleFacets Yulang.GeneralNominalHoleMaterialization Yulang.GeneralNominalHoleElimination
lake build Yulang
lake env lean Audit/GeneralNominalHoleElimination.lean
```

The new audit covers all 52 public theorems. Its dependency union is exactly
`propext`, `Classical.choice`, and `Quot.sound`. The five new modules are imported
by appended lines in `Yulang.lean`. Existing Lean bytes and frozen paths were
preserved. Branch and HEAD were unchanged. The final scope check and
`git diff --check` returned exit code **0**.
