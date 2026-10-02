# Finite graph presentation and principal safety certificates

Date: 2026-10-02
Status: Draft; research candidate; no implementation authority
Scope: finite heap abstraction and symbolic principal certificates
Approved-by: none
Drafted-by: primary, following bounded architect construction audit
Reviewed-by: compiler_referee and spec_auditor package review; accepted repairs checked by independent compiler_referee delta review (2026-10-02)
Supersedes: none

## 1. Claim and boundary

This package constructs a finite conservative carrier for a specified class
of heap machines, then proves a principal symbolic interface for an inductive
safety-certificate judgment on its graph. Exact concrete reachability is
unnecessary. Full successor applicability still needs source refinement,
a finite symbolic endpoint basis, modular interactions, and an acceptance
audit. The charter §§9, 11 permits researching this alternative; it has not
selected this abstraction or approved its possible rejections.

Prior art: Van Horn and Might, [Abstracting Abstract Machines, ICFP 2010](https://matt.might.net/papers/vanhorn2010abstract.pdf),
§§2.3–2.6, derives conservative analyses using store-allocated continuations
and finite abstract addresses. That technique informs the carrier. It does
not establish Yulang callback authority, symbolic family preservation, or
inference principality. The certificate proof below is a separate result.

Provenance classification: the heap abstraction is other primary-research
prior art, not a Simple-sub-original rule. The proposed certificate judgment
is a new successor candidate, whose generic theorem is proved below; its
application to Yulang remains conjectural. Its Boolean interface language is
not claimed expressible by ordinary Simple-sub bound schemes.

## 2. Explicit finite carrier

Fix a finite monomorphic ownership derivation `σ`, finite machine program,
and finite record/scalar signature. Existence of this derivation for arbitrary
successor source is not proved here. Store every recursive object as a heap
record: environment, closure, thunk, cell, call/handler frame, request, saved
suffix, lineage link, and pending-search/re-entry wrapper. Recursive fields
contain addresses, never recursively embedded records; each tag has bounded
arity fixed by the finite program.

Let `A` be finite addresses indexed by allocation site and object kind; `β`
maps each fresh concrete allocation to its site/kind. Let `D₀` be finite
scalar classes with a total abstraction `α₀` and computable sound primitive
tables. An opaque scalar class retains every possible test outcome. For
finite control sites `L` and lexical slots `X`, define:

```text
Env   = X -> A⊥
Rec   = finite tags with bounded fields from L, Env, D₀, A⊥,
        and fixed static type/request/boundary templates from σ
Store = A -> P(Rec)
Q     = modes × L × Env × Store × (A⊥)^r × finite auxiliary registers
```

Variable-length lists, stacks, searches, and continuations use heap links.
Identity/incidence summaries must also have a declared finite carrier. No
unbounded concrete identity or generated type term is hidden in a field.
Each `q` contains one joint store/root configuration; collecting states does
not globally join their stores. Address collisions can still lose concrete
correlations.

**Finiteness.** For `a=|A|`, `x=|X|`, `s=|Rec|`, with `j` remaining finite
control/register choices, `|Q| ≤ j (a+1)^x 2^(a s) (a+1)^r`. Records are
finite because all their fields are finite and recursion passes through
addresses. Cyclic heaps need no infinite syntactic unfolding. This proves
finiteness of the conservative carrier, not an exact regular quotient of
concrete heaps or practical efficiency.

## 3. Computable transfer and coverage

The concrete heap machine uses local instructions for register copy, record
construction, allocation, pointer lookup, field read/write, scalar operation/
test, branch, and jump. Unbounded walks use repeated instructions and explicit
pending state. No primitive may hide a concrete reachability oracle.

Define `c ≼ q` when concrete roots/registers map to the abstract ones and
every concrete record, with pointers/scalars mapped by `β/α₀`, occurs in its
abstract store entry. Extra abstract records are allowed. Transfers allocate
by weak insertion and enumerate records on lookup. Writes retain old records
and insert updated versions at every possible target. Scalar instructions
enumerate their finite sound table. Pointer comparison returns false for
distinct abstract addresses and permits both equality and inequality for
colliding addresses. A collision never proves two dynamic events,
activations, or cells identical. Copies, branches, and jumps follow the
selected abstract outcome. All these operations are finitely executable.

**Local simulation.** If `c ≼ q` and `c -> c'`, some abstract successor `q'`
has `c' ≼ q'`. Allocation follows by insertion; lookup includes the actual
record. Weak writes include the updated record and preserve the others.
Scalar-table soundness includes the actual scalar result. Equal concrete
pointers have equal `β` images; different pointers with colliding images also
retain the false branch. Copies and jumps are structural. These cases
exhaust the instruction set. Induction covers every finite instruction path.

This is the heap-machine theorem. The Yulang source refinement is still
open: it must implement ordered search, effectful guards, callback incidence,
invocation re-entry, and shallow forwarding/raw resume. Stored frames are not
necessarily active; activation follows current roots. Expiration cannot
delete every object allocated at one site. Raw resume must not explicitly
reinstall its consumed handler; collision-induced extra paths are
approximation, not source authority. Uncertain visibility must retain real
forwarding alternatives. Callback capture still requires a concrete contract;
`Force`, family equality, wildcards, and historical origin grant none.

## 4. Guarded graph and declarative interface judgment

Fix a finite predicate basis `P` over one type assignment `ν`, containing all
required source-family, operation compatibility, boundary-contract, and
primitive typing checks. Its Boolean algebra `B` is represented by truth
tables; unrealizable cells denote no actual assignment. Repeated execution
creates fresh events, not fresh static endpoints. Whether all successor rules
admit this finite basis remains open. Boolean tables alone do not decide
satisfiability in the underlying type theory.

Fix a finite observable index set `V` and a finitely/effectively supplied
`B`-valued relation `W` on `Q × V`. Supply formulas in `B` for the finite
abstract graph:

```text
Base(ν)   imported/lexical assignment premises
I_q(ν)    initial configurations
G_qr(ν)   declared abstract transitions
Bad_q(ν)  designated typing/safety obligation fails
W_qv(ν)   q contributes to joint observable interface tuple v
```

Split an event-bearing edge by a finite intermediate state when necessary.
Handler selection precedes and is independent of `OpCompat`; its selected
event has `Bad = ¬OpCompat`. Failure must not remove that edge or change it
to forwarding. `G` is exact for the declared abstract machine and may
overapproximate concrete transitions.

An interface `(A,U)` admits assignments `A` and bounds their joint observable
relation by `U`. Declare it derivable iff an invariant `H ∈ B^Q` satisfies:

```text
A ⇒ Base
A ∧ I_q ⇒ H_q
H_q ∧ G_qr ⇒ H_r
H_q ⇒ A
H_q ∧ Bad_q = false
π(H)_v := ⋁q (H_q ∧ W_qv) ⇒ U_v
```

This is one relational inductive-certificate judgment. Tuples `v` retain
joint views, not independently solved row/root marginals. Retaining the
whole graph as interface (`V=Q`, `W` identity) is the default finite case,
so no compact public row grammar is assumed. Full latent/future-use coverage
needs §7.
This proposed judgment has not been approved as successor acceptance.
Spurious incompatible paths can exclude concretely safe assignments; that
exclusion is not evidence of an actual source type error.

## 5. Principal-certificate theorem

Construct:

```text
R = μZ. (I ∨ Post_G(Z))
Reject = ⋁q (R_q ∧ Bad_q)
S = Base ∧ ¬Reject
H*_q = S ∧ R_q
U* = π(H*)
```

**Termination.** All formulas stay in fixed `B`. Per Boolean cell, `R` is
finite graph reachability and stabilizes within `|Q|` iterations from bottom
(zero for empty `Q`). A worklist adds at most `|Q| 2^|P|` state/cell pairs.
This excludes graph/basis construction and type-predicate satisfiability.
It gives a finite symbolic presentation even if those separate type-theory
decisions remain unresolved.

**Existence.** Initialization follows from `I ≤ R`. As each edge keeps `ν`
fixed, `S ∧ R_q ∧ G_qr ⇒ S ∧ R_r`, giving closure. `H*` implies `S` and
excludes all `Bad` by the definition of `Reject`. Projection is equality for
`U*`. Thus `(S,U*)` is derivable.

**Maximal admitted domain.** For any derivable `(A,U)` with witness `H`, path
induction gives `A ∧ R_q ⇒ H_q`. If an assignment satisfied `A ∧ Reject`,
some reachable bad state would satisfy `H_q ∧ Bad_q`, a contradiction.
Hence `A ⇒ S`.

**Minimal observations on every admitted domain.** The same induction gives
`A ∧ H*_q = A ∧ R_q ⇒ H_q`. Monotonicity of relational image yields
`A ∧ U* ≤ π(H) ≤ U`. Every derivable interface is a restriction of domain
`S` followed by a widening of its observable relation. Order interfaces by
reverse domain inclusion and observation inclusion on the narrower domain.
This comparison is a preorder. Quotienting by the same admitted domain and
equality of observations on that domain yields a partial order. Values of
`U` outside its admitted domain do not affect the comparison or leastness.
Then `(S,U*)` is least. This proves principality for the declared abstract
judgment, beyond untyped reachability leastness.

**Concrete safety.** Assume the following same-`ν` conditions, with
`c ≼_ν q` the concrete-to-abstract representation relation:

```text
∀ν,c. Initial_ν(c) ⇒ ∃q. I_q(ν) ∧ c ≼_ν q
∀ν,c,q,c'. c ≼_ν q ∧ c →_ν c' ⇒ ∃q'. G_qq'(ν) ∧ c' ≼_ν q'
∀ν,c,q. c ≼_ν q ∧ ConcreteBad_ν(c) ⇒ Bad_q(ν)
```

Initial coverage supplies a representative at the same assignment `ν`.
Guarded path induction using simulation supplies a reachable representative
for each concrete state on the path. Universal error reflection applies to
the actual reached representative: a concrete designated failure makes that
representative satisfy `Bad_q(ν)`. If `ν ⊨ S`, this contradicts the exclusion
of reachable abstract bad states. Thus admitted assignments have no
designated concrete failures under these premises. The Yulang premises are
not proved here. Full type safety requires coverage of every relevant source
fault and admissible interaction, not just `OpCompat`.

**Precision boundary.** Let `q0` be initial, `q0 -> q1` unconditional, and
`Bad_q1 = ¬p`. Then `S = Base ∧ p`. A certificate containing `q0` must
contain `q1`, hence imply `p`, even if this abstract edge is spurious for the
concrete program. The result is principal for this graph but not exact source
acceptance. Deleting the edge when `p` is false hides real incompatible
selection whenever present. Exact-acceptance quotient theorems correctly
exclude spurious rejection; they do not invalidate this abstract theorem.

## 6. Symbolic family discipline

One `ν` interprets premises, guards, compatibility, states, and output tuples.
No row/route witness independently chooses a shared family argument. Keep
all still-relevant predicates and their dependency graph with the interface.
For example, a reachable selected request requiring invariant predicate `p`
can disappear from residual support while `S` retains `R_selected ⇒ p`.
An empty row is not evidence for discharging that condition.

Projection eliminates control indices, not type assignments or live family
endpoints. Keep `(S,U*)` and the incidence graph together. Marginal rows are
derived views. Formula discharge and quantified-binder elimination are not
proved; generalization, freshening, and intrusion remain Milestone 4.

## 7. Remaining source and acceptance gates

The companion `2026-10-02-source-realization-and-symbolic-basis.md` constructs
the predicate inventory from a finite monomorphic descriptor graph and proves
selected-fault reflection for its encoding. Its §7 now constructs ordinary
visibility/query and shallow-control routines for finite linked resolved
templates. General adaptation, raw-source descriptor generation and unknown
future interactions retain their separate realization obligations.

The finite carrier, local simulation, and principal-certificate results close
their declared mathematical claims. Successor closure needs:

1. Refinement of ordinary source relations into the heap instructions,
   including computable typed visibility, expiration, and error reflection.
   Declaring `Visible` does not implement or finitely present it.
2. A finite endpoint/predicate basis from source ownership and operation
   instances. Generated type terms and arbitrary polymorphic instantiation
   cannot be concealed in finite fields.
3. Finite sound import/future-interaction summaries. Exported closures,
   latent thunks, and live-store resumptions must cover admissible clients,
   not just the closed call graph. The companion
   `2026-10-02-heap-backed-client-interactions.md` constructs a command-level
   driver for a supplied finite template-closed signature; deriving that
   signature for arbitrary source clients remains open.
4. A bridge to the intended source derivation preorder and Oracle final
   acceptance. Distinguish abstraction losses from actual source conflicts.
   No acceptance loss is approved by this research package.

For this generic heap machine with fixed finite symbolic inputs, presentation
size is finite per input and unbounded across inputs; infinite concrete
recursion is covered by cycles. This is a positive class-1 construction for
the declared abstract judgment, not a completed successor theorem or exact
class-2 quotient. No class-3 impossibility follows.

Choosing an abstraction determines the proposed analysis semantics. A later
budget on constructing/saturating it is separate: deterministic exhaustion
must report inference-complexity failure without partial publication, silent
coarsening, or labeling the source ill-typed. Thresholds and compiler
implementation remain unselected.
