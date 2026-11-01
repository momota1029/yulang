# R222 equation packet, revision 1

Status: **frozen candidate equations; exact guardedness/correspondence obstruction**.
Author: `/root/r222_equations`, no descendants. Requested runtime: registered
`prover`, Sol/high; observed model/effort: UNKNOWN/UNKNOWN. This is mathematical
and source inspection, not a checked Lean proof or independent certification.

## Parent and application

The unchanged roots are `YulangClosure.SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination` in
`YulangClosure/Contracts.lean:128–154`. Their original supported-source, scope,
shared-witness, solution and instance quantifiers remain unchanged. No result
here is applied to one of those roots: **parent delta 0; 0/4 roots, 0/5 packages**.
The intermediate R212 dependency is construction of one graph and reference
assignment from `AbstractCore.CoreState`, rather than an externally supplied
valuation, successful history or graph solution.

R222's stop condition is reached before an admissible complete compiler can
be frozen: the literal paper equation for an input emitted by R212's actual
partial operation contains a lattice-only cycle. The pinned target requires
every lattice-only path to terminate structurally. This is a failure of the
direct equation encoding and a missing normalization/correspondence theorem;
it is **not** a proof that the input store has no model or that every possible
semantics-preserving encoding is impossible.

## Sources and fixed interfaces

Read authority: `2026-10-11-yulang-inference-top-level-principles.md` §§1–3,
root AGENTS and pre-sprint map, `rules/goal-driven-sprints.md`, agent-loop
README and R222 contract. The actual paper is Lionel Parreaux, *The Simple
Essence of Algebraic Subtyping*, PACMPL 4, ICFP, article 124 (2020), local
original `/home/momota1029/rust/simple-sub-reference-paper.pdf`.
Read Fig. 10 and §§5.1.1–5.1.2, printed pp. 124:24–25, and Figs. 11–12 plus
§5.3.1, printed p. 124:26. Extracted with `pdftotext -layout … -`; no extracted
file was written. The paper explicitly permits unguarded recursive syntax;
its restrictions concern use of recursive subtype hypotheses. It does not
identify arbitrary such types with a selected least or greatest fixed point.

`CoreState` contains finite bounds, levels and representative tables, but no
complete Step/Run/Accepted relation. `insertPendingUpper` resolves the lower
variable once through the representative table, checks dependency levels,
inserts its upper bound, and replays existing lower bounds. It does not filter
the self-bound used below. This packet uses no hypothetical future transition.

`Lattice.Node` has structural, union and intersection nodes, with separate
Value and Effect tables. `Lattice.Graph.Valid` checks existing children and
unique record labels/variant tags. `Lattice.Graph.Guarded` additionally requires
`FiniteLattice graph kind index` at every allocated node. Its inductive cases
stop at a structural node or require **both** lattice children to have finite
derivations. Structural recursion may cycle; union/intersection recursion may
not. Neither Valid nor Guarded is supplied by the input.

`LatticeInference.References` is `Kind → Nat → Nat`, one assignment shared by
all constraints. `decodeTerm` retains all four Function ports. Its row spines
flatten to finite whole lists; a record tail must decode as a record, a tuple
tail as a tuple, and variant payloads as a tuple. These are real interface
requirements, not hypotheses silently supplied as `Completion.LawfulStore`.

## Literal, finite contextual equations

Write `q_k(i)` for the actual one-step representative lookup and `row_k(r)`
for the actual row lookup. Let a polar key be `(k,r,p)`; kinds are part of
identity. On finite inputs whose lookups exist, define the following candidate
syntax algorithm `E_C^p(t)`, with a finite set C of active polar keys. A binder
occurrence receives a fresh lexical occurrence ID in addition to its printed
row/polar name. Bound occurrences resolve to the matching active binder;
nested binders with the same printed key must not be identified by spelling.

For variable i, resolve r=q_k(i). If `(k,r,p) ∈ C`, return its bound occurrence.
Otherwise the **literal Fig. 12 equations** are:

```text
E_C^-(var i) = μ b_(k,r,-).
                 foldl Intersection Top
                   [ E_(C∪{(k,r,-)})^-(u) | u ∈ row_k(r).upperBounds ]

E_C^+(var i) = μ b_(k,r,+).
                 foldl Union (E_C^-(var r))
                   [ E_(C∪{(k,r,+)})^+(l) | l ∈ row_k(r).lowerBounds ]
```

The second seed is evaluated under **C**, not `C∪{(k,r,+)}`. To use `var r`
without a second, different representative resolution one needs idempotent
representatives; alternatively the helper takes the already resolved row r
and does not resolve again. The latter is the literal row-state formulation.
Bounds retain their stored order and multiplicity. The seed is Top only for
negative coalescing; ordinary free row names are not common solutions.

Atoms, Bottom, Top, Union and Intersection preserve their constructors.
Function is exactly

```text
E_C^p(Function(a,ae,re,r)) =
  Function(E_C^(flip p)(a), E_C^(flip p)(ae), E_C^p(re), E_C^p(r)).
```

RecordCons retains label and optional bit and maps both children with p;
TupleCons maps head/tail with p; VariantCons retains tag and maps payload
spine/tail with p. All three nil constructors are retained. Effects keep the
same kind throughout; no untyped integer is used as a cross-kind reference.

This gives a finite recursive-equation **presentation**, by expanding the
finite contextual syntax and then naming its binder bodies. Finiteness uses
the finite key set of size `2*(valueRows.length+effectRows.length)`, structural
subterm descent, and the fact that only the positive-to-negative seed can keep
C unchanged at a row expansion. That seed decreases a phase rank; all bound
expansions add their absent key. A lexicographic construction measure is
`(number of absent keys, structural term size, positive-seed phase)` after
resolving the current row. This is a mathematical termination argument, not a
checked fuel bound for R212's existing `2*N+1` fuel.

The compact simultaneous shorthand `N_r = meet(U_r^-); P_r = N_r join L_r^+`
is a useful candidate sharing transformation. It is **not** substituted for
the contextual equations without a full lexical/context equivalence theorem.

## Direct graph/reference encoding and its boundary

The attempted exact encoding allocates constructor occurrences separately in
each kind table. A recursive binder itself introduces no new structural
constructor; its reference denotes the root of its body. A bound occurrence
points back to the body of its lexical binder. Union/intersection allocate
their corresponding two-child nodes. Atoms, extrema and Function allocate
their exact existing structural nodes. Finite row spines flatten to the exact
Field/Alternative lists, preserving labels, optional bits, tags, payload order
and tuple order. Variable references are pulled back along q, rather than
chosen independently per use or per clause.

At this point the encoding can produce a finite graph satisfying Valid while
failing Guarded. The success test `checkGraph && checkGuarded` is constructive
and non-circular, but rejecting every such failure is not an admissible source
domain justification: the following failure is emitted by the actual admitted
partial transition. No complete accepted domain or structural-store theorem
is claimed by this packet.

Duplicate representatives remain an additional preservation seam. For example,
q=[0,0] with nonempty bounds in row 1 must not lose those bounds merely because
`coreCoalesce` reads row 0. Class-bound concatenation is computable, but requires
an equality/merge correspondence proof; no actual R212 merge operation supplies
one yet. No duplicate representative is excluded to repair the main claim.
The minimal obstruction below has identity representatives, so it does not
depend on this seam or any malformed row spine.

## Smallest emitted obstruction

Use the actual `CoreProblem` data:

```text
demands      = [⟨⟨value, var 0, var 0⟩, origin=0, receiver=0⟩]
valueGraph   = births [0], references []
valueLevels  = [0]
effectLevels = []
publications = []; uses = []
```

`inputValid` is true: both endpoints exist, all variable occurrences are
allocated, and the reference table is valid. `initial` gives representative
[0], one level-0 row, retained clause `var 0 <: var 0`, and an active pending
demand. `insertPendingUpper` succeeds because 0 ≤ 0. It produces
`upperBounds=[var 0]`, `lowerBounds=[]`, `pending=[]`, with unchanged allocation,
representative, level and retained store. This state is an actual constructor
output; it is not claimed to be the output of a nonexistent full Accepted run.

At the paper's singleton-meet notation, the exact **syntactic** negative
result is `μn.n`. In the explicit fold convention above (also used by R212),
the corresponding syntax retains the neutral Top seed:

```text
E_∅^-(x) = μn.(Top ∩ n).
E_∅^+(x) = μp.(μn.(Top ∩ n)).
```

Thus `μn.(Top∩n)` is the explicit finite-meet presentation of the paper's
equation, not a checked theorem equating recursive types in the pinned graph
semantics. The paper's raw `μn.n` has an alias-only loop and no constructor
root to allocate; retaining the Top seed yields the concrete failing graph
below. Either presentation exposes the same missing guarded compilation step.
No claim `μn.(Top∩n) ≡ Top` or `μn.n ≡ Top` is made.

With Value root 0 and Top at 1, the exact direct graph is

```text
g value  = [intersection 1 0, structural Top]
g effect = []
refs value 0 = 0.
```

This graph is Valid. It is not Guarded: any `FiniteLattice g value 0`
derivation must end in the intersection constructor, whose right premise is
again `FiniteLattice g value 0` with a strictly smaller derivation. Induction
on that finite derivation gives a contradiction. This argument needs no
subtyping assumption, model choice, successful history or supplied graph.
The same construction works for one Effect row, with the node tables swapped.

The retained store itself is reflexive and has many solutions, including Top.
Therefore this is **not** an inconsistency counterexample. Replacing this
literal recursive body by Top is an additional normalization. Neither the
pinned interfaces nor the paper's allowance of unguarded syntax proves that
normalization source-equivalent. The first missing result is precisely that
guard-producing normalization/correspondence, or an actual transition invariant
which prevents this emitted self-bound. The existing insertion prevents none.

## Required discriminators

These are hand-derived equations/targets, not executed fixtures.

| Input | Literal consequence and discriminator |
| --- | --- |
| Upper-only `U_x=[Int]`, `L_x=[]` | N=`μn.(Top∩Int)`, P=`μp.N`; direct finite guarded graph exists. The R212 Bool-free-name shortcut is rejected: ordinary `Bool <: Bool∩Int` does not follow. |
| Bound-only `U_x=[x]` | Exact minimal lattice self-cycle above; both kinds independently exhibit it. |
| Two-row `U_x=[y], U_y=[x]` | `μn_x.(Top∩μn_y.(Top∩n_x))`; retaining both bounds leaves a lattice-only cycle even if a future transition filters immediate self-bounds. |
| Recursive Function `U_x=[F(x,e,e,x)]`, e unbounded | Negative literal root is `μn.(Top∩F(n,Top,Top,n))`, up to vacuous binders. Both Function Value ports and both Effect ports remain present; the recursive Value edges cross Function. |
| Mixed polarity: positive readout of that Function row | Literal P=`μp.μn.(Top∩F(μp'.n,Top,Top,n))`; R212 extra-seen P=`μp.μn.(Top∩F(p,Top,Top,n))`. This is a syntactic discriminator, not a claimed semantic counterexample. |
| Four distinct ports `F(x,e,f,y)` with distinct row bounds | Positive traversal uses `(N_x,N_e,P_f,P_y)`; negative traversal uses `(P_x,P_e,N_f,N_y)`. Ports and kinds cannot be merged. |
| Combined Value/Effect recursion | Keep `U_x=[F(x,e,e,x)]` and `U_e=[e]`. The Value structural cycle and Effect lattice cycle coexist; the Effect cycle still fails Guarded. |
| Duplicate representatives | q=[0,0], bounds in both physical rows require an explicit bound-preserving merge rule, not dropping row 1. |

An SCC containing both Value and Effect vertices cannot be generated by the
current Term grammar: Value Function nodes can point to Effect, but every
Effect term consists only of Effect variables/atoms/extrema/lattice constructors,
so it has no edge back to Value. This follows by induction on `Term .effect`.
The combined fixture represents both kinds' cycles without inventing an
unavailable cross-kind constructor. Record/tuple/variant constructors are
retained in the equation traversal; full finite-spine normalization and its
scope remain unproved, rather than assumed through LawfulStore.

## Exact theorem targets and unresolved owners

No declaration below has been added to Lean or checked. The complete compiler
target would have the shape

```lean
buildSharedReadout : CoreState → Option (Lattice.Graph × LatticeInference.References)

-- Required conclusion, not an input law:
buildSharedReadout state = some (graph, refs) →
  graph.Valid ∧ graph.Guarded ∧
  (∀ kind identity, identity < (state.rows kind).length →
    Lattice.Exists graph kind (refs kind identity)) ∧
  ExactFig12Interpretation state graph refs ∧
  LatticeInference.StoreSatisfied graph refs state.retainedConstraints
```

`ExactFig12Interpretation` is a required yet undefined correspondence relation,
not a packaged assumption. The compiler success/domain must come from the
actual construction and independent input checks; no theorem is delivered by
assuming this relation, Store.Satisfied, LawfulStore, successful history or a
solution. Original-store interpretation also requires connecting retained
constraints to all normalized bounds and completing structural consistency
propagation. Arbitrary CoreState data have no such invariant today.

A focused next Lean packet, if Luna admits it, could define the displayed
two-node graph from the actual emitted state and prove:

```lean
-- Exact proposed targets, absent declarations:
selfUpperProblem.inputValid = true
selfUpperProblem.initial.insertPendingUpper = some selfUpperState
selfUpperGraph.Valid
¬ selfUpperGraph.Guarded
```

This would formalize the obstruction, not close R222 or its parent. The proof
leaf currently owns no Lean/build/cache paths; no execution was assigned here.

Mutual TODO R222-GUARD (owner Luna to assign): derive a finite normalization
from literal contextual equations and prove its correspondence on emitted
bound-only cycles. Exact falsifier: the displayed one-row output must be
represented without claiming its failed Guarded proof or excluding its input.
Required inputs: literal Fig.12 plus current FiniteLattice/graph semantics;
output: checked normalization/correspondence theorem, or a precise source-
qualified obstruction. New graph semantics or enlarged dependencies need Luna.

Mutual TODO R222-ROW-MERGE (future equality-transition owner): show all physical
row bounds survive representative merging and are reflected by the single
reference pullback. Falsifier: q=[0,0] with a unique retained bound on row 1.
This is independent of R222-GUARD and is not resolved by a local frame action.

## Reuse, execution and freeze

Reused R212's actual input/row/insertion definitions, upper-only and four-port
discriminators, and its independently recorded unresolved Fig.12 seam. Rejected
ordinary-free-name uniformity, supplied solution/history hypotheses, and treating
the candidate shared simultaneous equations as an already proved equivalence.
R221's original-source carrier obstruction remains intact and independent.

Read-only commands: source `cat`/`sed`/`rg`, paper extraction to stdout, and
SHA-256 reads. No Lean, Lake, tests, Cargo, Rust, Git, network, scratch file,
environment or cache write occurred. No theorem/axiom audit was executed;
delivered checked theorem set and complete axiom lists are both empty.
Budget: ≤900 seconds; no worker, descendant or heavy process started.
Only this artifact and the exact assigned inbox path are written.

Dependency hashes and final artifact hash are recorded in that inbox receipt.
The final step is a primary-owned boundary adjudication, not self-certification.
**WRITES_STOPPED** after the revision-1 handoff freeze; no descendants or unresolved
descendant leases. No original parent is closed.
