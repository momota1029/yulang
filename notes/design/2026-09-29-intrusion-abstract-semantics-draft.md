# SCC intrusion abstract semantics — first draft

Date: 2026-09-29
Status: Draft; exploratory; not implementation authority
Scope: pure polarized type graphs and definition-SCC generalization
Approved-by: none
Approved-at: none
Drafted-by: primary agent
Reviewed-by: none
Supersedes: none

This draft advances Gate B of
[`2026-09-29-scc-intrusion-redesign-charter.md`](2026-09-29-scc-intrusion-redesign-charter.md).
It records a candidate mathematical interface, not a settled representation or
a soundness/principality result. F5 closed schemes are not the target.

## 1. Initial graph class

Start with finite regular graphs: cycles are represented by back-edges, never by
unfolding. The first proof fragment contains only `Bottom`, `Top`, atomic
constructors, variables, and polarized Functions. Function arguments reverse
polarity; results preserve it. Records and tuples may be added as covariant
products after the core lemmas. Effects, rows, methods, role constraints, and
handler hygiene are outside this fragment.

The graph has two kinds of identity:

- a **type vertex** identifies one shared unknown and owns its lower and upper
  bound edges;
- a **boundary port** identifies one independently substitutable exposure of
  that graph at a generalization boundary.

An edge occurrence records a polarized type endpoint, its direction, stable
source/proof identity, and any weight annotation. An endpoint is a constant, a
constructor applied to endpoints, a Function of endpoints, or a reference to a
type vertex. A lower edge records `endpoint <: vertex`; an upper edge records
`vertex <: endpoint`. Which lower occurrences are eligible for a scheme root
is a separate evidence-sensitive projection decision; it is not implied by
mere presence in the structural bound graph. The initial graph `G₀` is the
closed SCC state at the quantification boundary. Root generalization may then
add constraints and restart. Each member result is tied to the point where the
Oracle produces it; later roots may advance the shared solver state. The final
component publication boundary follows completion of all ordered root
preparation. The precise relation among the saved result, later constraints,
and proof state remains to be defined.

### Oracle closure relation for the fragment

The Oracle's constraint entry takes a positive endpoint `p` and a negative
endpoint `n`, and records the obligation `p <: n`. In the variable-only cases,
the audited closure rules are:

```text
Var(v)+ <: Var(w)-, v != w:
    add Var(v)+ to lower(w)
    add Var(w)- to upper(v)

Var(v)+ <: n, n not Var:
    add n to upper(v)

p, p not Var <: Var(w)-:
    add p to lower(w)

Var(v)+ <: Var(v)-:
    no new bound
```

Bounds are installed before propagation continues. Structural constraints add
subtype obligations until the worklist reaches its fixed point. For pure
Functions, `Fun⁺(a⁻, r⁺) <: Fun⁻(a⁺, r⁻)` adds `a⁺ <: a⁻` and `r⁺ <: r⁻`;
the argument obligation reverses direction and the result obligation keeps it.
For the finite core used here, `Bottom <: n` and `p <: Top` close immediately;
`(p₁ ∪ p₂) <: n` adds both branch obligations; `p <: (n₁ ∩ n₂)` adds both
upper-branch obligations; and equal nominal constructor heads add the
declared invariant argument obligations. Mismatched nominal heads and all
effect/row cases are excluded from this first graph class.
This records the Oracle's operational constraint relation for the fragment,
not a denotational model of all possible runtime types. The source audit and
the SCC scheduling observations are recorded in the behavior ledger.

The candidate intrusion proof must show that parent/overlay construction
preserves this closure relation after projecting each component root. It must
not replace the two variable-bound insertions with an equality edge merely
because both mention the same graph vertices.

## 2. Enclosing environment and closure

For each member definition `d`, use its own generalization boundary `B_d` and
enclosing environment `E_d`. The Oracle derives `B_d` from the member's
`BindingFetch`: `FetchValue` uses the root boundary, while `FetchComputation`
uses its child. SCC membership alone does not imply identical fetch or
boundary state. Relative to `(d, B_d, E_d)`, divide vertices into:

- **local** vertices allocated in the SCC being generalized;
- **outer** vertices owned by an enclosing environment;
- **rigid** vertices whose identity must remain shared and cannot be selected
  by this generalization.

`E_d` also includes identities retained at a unit boundary. Oracle's computed
fetch fixture carries such a variable through the unit cache interface as a
boundary binder rather than a per-use quantifier. When imported into a unit,
that boundary identity is mapped once and then shared by uses in that unit.

The environment is part of the semantic input, not copied into the SCC. A local
vertex that reaches an outer/rigid vertex through either bound direction keeps
that exact outer identity. It must not receive a fresh local parent merely
because the path crosses the boundary. Reachability includes recursive and
shared back-edges and is graph traversal, not path enumeration.

While an SCC is open, references among its members point to their live roots;
an internal use gets no use-site substitution. The Oracle then processes
member roots sequentially during component quantification. A root's generalizer
can add constraints and restart before producing that root's result, so a later
member can be processed at a newer constraint epoch. The root results are
collected before member schemes are installed, and incoming uses are routed
only after that collection. The Oracle therefore supplies an all-member
visibility barrier, but does not establish one immutable graph snapshot shared
by every member view.

The semantics must account for this sequential preparation behavior, but a
replacement need not reproduce Oracle's internal mutation protocol. One
sufficient candidate is a versioned shared SCC graph: each root step reads
the current version, performs root-local projection/prepasses, saves the member
result at the point Oracle produces it, and passes the updated state to the
next member step. The saved result need not describe the final solver epoch:
Oracle has bounded post-loop passes that can add constraints without
restarting that root's generalization. After every view is prepared, install
all member views before processing incoming uses; final slot writes may remain
sequential behind that visibility barrier. Incoming uses select the matching
member view and allocate independent overlays. A different implementation may use another schedule if
it proves the same observable member results, later-root behavior, and
incoming-use behavior. Whether graph versions can share all unchanged SCC
vertices without losing an Oracle-observable update remains unproved. This
candidate replaces the earlier single-snapshot assumption and is not selected.

## 3. Parent ports are not aliases

The operation under study is a boundary map, not variable equality. Oracle
generalization uses member-specific boundaries. In separate sessions, the same
child-level identity-Function graph is quantified under `FetchValue` and
retained at the unit boundary under `FetchComputation`. It is not yet
established that one accepted SCC can expose the same TypeVar to members with
both fetch modes; a computed-fetch cycle can diagnose. If that mixed member
topology is admitted by the supported envelope, a synthetic shared vertex is
a counterexample to a single component-wide quantification bit. The root
lifecycle must preserve diagnostics that reject computed-fetch cycles.

The candidate therefore indexes port selection by member:

```text
Gen_d = this member's surviving quantified variables after root projection,
        role reachability, and final pruning
Free_d = surviving non-quantified variables, including unit-boundary identities
Erase_d = one-sided variables replaced by the root projection's polarity extreme
Cycle_d = member-local recursive identities needed to preserve regular bounds
Local_d = Gen_d ∪ Cycle_d
Phi_d : Local_d -> fresh member-owned ports
P_d = Phi_d restricted to Gen_d; C_d = Phi_d restricted to Cycle_d
```

The map's domain is the source identity, not the role-tagged pair: if `v` is
both in `Gen_d` and a recursive root in `Cycle_d`, then `P_d(v) = C_d(v)`.
Distinct source identities still receive distinct ports. `Free_d` and `Erase_d`
must be disjoint from `Local_d` in a valid member view. On imported views, a
boundary identity that collides with a per-use generalized or recursive
identity is rejected rather than silently captured; the Oracle validates this
at `instantiate.rs::validate_imported_scheme_vars` with a per-use-boundary
collision error.

The audited Oracle quantifier predicate requires `level(v) > B_d` and excludes
non-generic variables; reachability through the member's projected root and
applicable role constraints also matters. Simplification/pruning can remove a
candidate that does not survive in the member result. The source path is
`generalize/mod.rs::quantified_vars_in_root_and_roles` and its caller in
`analysis/session/generalize.rs`.

Within one member view, `P_d` is injective: every occurrence of the same
quantified TypeVar, including both Function polarities, maps to one port.
Different members own distinct semantic ports even when they select the same
source TypeVar. `Free_d` variables remain anchored through `E_d` to their
shared/session identity. `Erase_d` occurrences follow the root's polarity
projection and disappear to `Bottom` or `Top`; they do not become free ports.
The Oracle's separate-session observation is in
`analysis/tests/case_03.rs::computed_fetch_def_does_not_quantify_binding_level_root`.
Whether the corresponding same-SCC topology is source-valid remains open.

The Oracle separately freshens recursive-bound identities on each use. A
nominal-guarded source SCC with zero ordinary quantified variables and one
recursive bound is recorded in the ledger. Separately, the manual scheme
fixture `analysis/tests/case_02.rs::oracle_a1_stage_3_exit_preserves_q_r_and_b_lifetimes_across_imported_uses`
checks that Q and recursive-bound R identities are fresh across two uses while
B remains shared. The zero-Q/one-R source shape has not yet been exercised
with two incoming uses. The replacement therefore needs `Cycle_d` ports or a
proof that its regular graph back-edges provide the same per-use freshness
without separate binders. `Phi_d` maps each source identity only once, so if
one identity appears in both `Gen_d` and as a recursive root, both roles use
the same port. It is injective on distinct source identities. Each incoming
use freshens member-local `Local_d` identities independently; non-quantified
boundary identities continue through the environment mapping shared by the
compilation unit.

An implementation may intern backing storage for parent vertices across
members, but eligibility and lookup must remain keyed by member. A single
component-wide `TypeVar -> port` decision cannot express the distinction among
`Gen_d`, `Free_d`, and `Erase_d`. Lower and upper edges still transport
separately through each `P_d`; recursive edges preserve `C_d`; an outer/rigid
or free endpoint keeps its anchored identity. The closure criterion that
selects these sets is not proved: it must account for root reachability,
polarity elimination, the member's boundary, recursive projection, and later
evidence/role projection. The parent relation does not erase the original
graph vertex or its edges. In particular, `local == parent` is not an allowed
interpretation: it would identify identities without establishing that
lower/upper approximations are preserved.

`Gen_d`, `Free_d`, `Erase_d`, and `Cycle_d` describe distinct behaviors even
if an implementation stores some of them in one table. For a type-variable
occurrence, a `Gen_d` member uses `P_d`, a surviving `Free_d` member uses
`E_d`, and an `Erase_d` occurrence becomes its polarity extreme. A recursive
back-edge uses the corresponding `C_d` identity. An identity may serve more
than one structural role; `Phi_d` and the per-use map must preserve that
aliasing while freshening all member-local generalized and recursive
identities.

### Edge-transport lemma for an injective parent map

Let `rho` rename every selected local variable to a fresh parent, leave all
other variables fixed, and map every type-expression node homomorphically while
memoizing node identities. Require parent IDs to be fresh and pairwise
distinct. Transport both lower and upper edge sets by `rho`; do not delete the
original frozen graph. Let `C(S)` be the least closure of a finite set `S` of
subtype obligations under the fragment's variable, Function, union,
intersection, and same-head invariant-constructor rules.

**Claim.** `C(rho(S)) = rho(C(S))`.

**Proof sketch.** Every closure rule is local to its endpoint constructors and
variable IDs. `rho` preserves constructors, polarity, and variable equality;
freshness prevents a renamed local variable from colliding with an outer or
rigid variable. Therefore each rule step `S -> S'` maps to the same rule step
`rho(S) -> rho(S')`. Conversely, `rho` is injective on the renamed graph, so
each rule step in the image has a unique preimage. Induction over finite closure
steps gives equality of the two closures. The fast path for
`Var(v)+ <: Var(v)-` is preserved because injectivity preserves exactly which
endpoints are the same variable.

This proves that alpha-renaming the bound graph to fresh parents neither loses
nor adds closure edges. It does **not** prove that the selected parent set is
the Oracle's generalizable set, that root projection is principal, or that
retaining both bound directions matches one-sided Oracle approximations. Those
are separate lemmas and remain the central semantic risks.

An earlier finite Python model was removed from the active research artifacts.
Its checks did not execute the Rust solver or the Oracle and are not evidence
for this lemma. Closure transport is currently only the written proof sketch
above; it still needs a Rust characterization or a complete mathematical
argument against the defined graph rules.

### Candidate root-local polarity projection

The Oracle source gives a concrete projection behavior to model. For each
member root separately, it starts at positive polarity. A variable side is
expanded through lower bounds when positive and upper bounds when negative;
recursive visits are detected by `(TypeVar, polarity)` and represented by a
back-reference plus its recursive bound. Function arguments flip polarity and
results preserve it; unions are positive joins and intersections are negative
meets. After that root's reachable regular graph is built, the Oracle collects
variable polarity over the root and recursive bounds. A generalizable variable
seen at only one polarity is erased to that polarity's extreme (`Bottom` when
positive, `Top` when negative); a variable seen at both polarities remains
shared. Boundary/non-generic variables are excluded from this erasure.

The intrusion candidate must run this projection per member root over an
immutable shared component graph. Polarity census for one root must not absorb
occurrences belonging only to another SCC member: the Oracle produces one
generalized result per member, even though the component is solved together.
The internal result may remain a regular graph with parent references; it need
not copy the Oracle's closed scheme encoding. The semantic obligations are to
preserve the root-local reachability, recursive back-references, one-sided
extremes, and shared identity of bipolar variables. Oracle source probes
establish only the exact programs listed in the behavior ledger. No executable
intrusion model currently establishes this projection rule, and it does not
prove principality.

### Alpha-renaming commutes with the pure root projection

Here `Project` means `compact_root_for_scheme` graph collection followed by the
polarity census and one-sided-variable elimination described above. It does
not include the Oracle's other simplification passes such as coalescing,
pinned-interval collapse, sandwiching, or role processing.

The audited Oracle projection path provides a stronger lemma for the first
pure graph fragment. Let `G` be the already scope-filtered, frozen lower/upper
graph for one generalization boundary; this lemma does not prove that
`scheme_projectable_lowers_in_scope` selects the right edges. Let `rho` be an
injective renaming from selected local variable IDs to fresh parent IDs. Assume
it preserves each variable's generalization-candidate predicate
(`level >= boundary && !non_generic`), maps the selected root, and renames
every edge occurrence in `G` without changing its direction, constructor,
weight, stable source record/evidence, or iteration order. The already selected
edge occurrences and their order are part of this lemma's input: the Oracle
collector processes lower-bound records in order, and recursive-side bounds
are stored by `(TypeVar, polarity)` even though cache keys also include weight.
`rho` is the identity on outer/environment variables.
Then the Oracle root projection commutes with `rho`, up to alpha-equivalence
of recursive-side ordering:

```text
Project(rho(G), rho(root), rho(environment))
    = alpha(rho(Project(G, root, environment)))
```

Reason: the collector cache is keyed by `(TypeVar, polarity, weight)`, while
recursive re-entry and the recursive-side set are keyed by `(TypeVar,
polarity)`. Injectivity preserves equality and inequality of variable IDs in
both key spaces; keeping annotations, source record decisions, and iteration
order fixed maps every structural descent to the same polarity descent and
preserves which weighted visit records each recursive side. Thus cache hits,
recursive re-entries, and recursive-side membership commute with renaming,
and the root and recursive-side table are renamed homomorphically. The
following polarity census also commutes with renaming. Finally, its
elimination predicate is `level >= boundary && !non_generic`, so preserving
that predicate preserves exactly which occurrences are eligible; one-sided
versus bipolar status is unchanged. Recursive-side serialization order may
differ because the Oracle sorts by numeric TypeVar ID, which alpha-equivalence
deliberately ignores.

The implementation evidence is
`compact/collect/mod.rs::compact_root_for_scheme,compact_var_side` and
`compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic,
is_simplification_candidate` in the frozen Oracle at `a58eefc3`. This lemma
supports preallocating injective parents before visiting roots in any order,
provided parent metadata preserves the candidate predicate and the frozen edge
selection is already correct. It proves renaming invariance for projection,
not edge selection, the parent set, instantiation overlays, SCC scheduler
equivalence, or principality.

### Oracle lower-edge selection is evidence-carrying

The frozen Oracle does not project every structural lower-bound record
unconditionally. In scheme mode, `compact_var_bounds` asks
`scheme_projectable_lowers_in_scope` for each variable's lower records. That
query preserves an unclaimed record, discards a record whose `project_lower`
decision is `Excluded`, and keeps an `Included` record with support/evidence
metadata. Missing or inconsistent proof state is a fallible projection error,
not an implicit inclusion.

Consequently an intrusive graph cannot model the full Oracle boundary as only
`(owner, direction, endpoint, weight)`. The selected edge occurrence also has
source record/proof identity. Some proof carriers refer to constraints, replay
derivations, claims, and type-variable pivots. There are three possible
transport designs to prove: transport and validate these references together
with type endpoints; select and validate edges on the original graph for each
root/epoch attempt, then pin the selected ordered edges to that view while
parent-renaming; or define replacement-owned evidence that makes the same
include/exclude decision. The second route depends on retaining the graph and
proof snapshot queried for that root view. The collector consumes the selected
bounds after the query and does not inspect their reason/evidence payload
during structural collection. Thus copying only final structural edges is
justified only when the selection decision and snapshot remain attached. The Oracle entry
`compact_type_var_for_scheme` creates a fresh projection-evaluation round and
scoped query for each compaction attempt. Root generalization can repeat at
newer constraint epochs, so a preselection cache shared across member roots
must prove that it preserves each root's ordered decisions, failures, and
epoch-specific graph view. Otherwise selected-edge decisions remain attached
to each root attempt.

This adds a separate proof obligation before claiming ordinary Oracle
capability: characterize when lower records are Unclaimed, Included, or
Excluded in the supported pure input envelope, then show a selected-edge
transport design preserves that decision and its failure behavior. Restricting
the first envelope to unclaimed pure edges is a possible research boundary,
but it is not chosen here; it would need source-level coverage and an explicit
compatibility limit before implementation. Source locators at `a58eefc3`:
`constraints/structural_kernel/access.rs::scheme_projectable_lowers_in_scope`,
`compact/collect/mod.rs::compact_var_bounds`, and
`constraints/proof/mod.rs::project_lower_inner`; the per-root projection round
is created by `compact/surface.rs::compact_type_var_for_scheme`. Proof payload
types are in `constraints/mod.rs` and `constraints/proof/mod.rs`.

## 4. Instantiation uses overlays

An instantiated use of member `d` receives a fresh overlay `sigma_(d,u)` for
that member's `Gen_d` and `Cycle_d` identities. All occurrences of one identity
in that use consult the same overlay entry; another incoming use gets disjoint
generalized and recursive substitutions. A non-quantified boundary identity
resolves through `E_d`, retaining the sharing the Oracle gives free variables
and imported unit binders. Each selected member view is read-only during use
instantiation.

Constraints produced by the use are attached to generalized or recursive
overlay endpoints; they must not mutate another use's overlay or the selected
member view. Constraints reaching identities in `E_d` remain intentionally
shared. This is the current isolation invariant for the candidate model; it
still needs a formal preservation proof against the Oracle's use behavior.

### Conditional factorization lemmas for an exact member view

Assume root preparation has already produced a finite regular member graph
`H_d` with its selected ordered edges, recursive back-edges, and one-sided
occurrences projected exactly as specified for that member. This assumption
does not prove Oracle edge selection or root preparation. Let `R_d` be the
source TypeVar identities visited while preparing the root, and `V_d` the
identities that still occur in `H_d`. Every member of `V_d` must be in
`Gen_d ∪ Free_d ∪ Cycle_d`; `Gen_d ∩ Cycle_d` is permitted, while `Free_d` is
disjoint from `Gen_d ∪ Cycle_d`. `Erase_d` is a subset of `R_d \ V_d` whose
root occurrences were replaced by the appropriate polarity extreme. Other
pruned identities need not be in `Erase_d`.

For a use `u`, define `rho_(d,u)` on the surviving identities:

- `Gen_d ∪ Cycle_d`: map through the single source-identity map `Phi_d`, then
  through this use's fresh substitution `sigma_(d,u)`;
- `Free_d`: map to its stable identity in `E_d`.

No `Erase_d` variable occurs in `H_d`; its extreme node is copied as a
constructor leaf. This keeps erasure separate from the injective variable
renaming.

Constructor nodes and both edge directions are copied homomorphically. Stable
source/proof identities and edge order are retained; any type-variable
payload in evidence uses the same variable map. A source identity that belongs
to both `Gen_d` and `Cycle_d` is mapped once through `Phi_d`. The resulting
variable map must be injective over identities still present in `H_d`: distinct
local identities receive distinct fresh IDs, environment identities retain
their identity, and no fresh ID collides with `E_d`. A boundary collision is a
view-construction failure, not implicit capture.

**Closure transport.** For any finite set `S_d` of subtype obligations formed
from `H_d`, and the well-formed injective renaming `rho_(d,u)` above, the
closure under the finite graph rules commutes with the map:

```text
C(rho_(d,u)(S_d)) = rho_(d,u)(C(S_d))
```

The proof is the local-step argument from the edge-transport lemma: constructors
and polarities are unchanged; injectivity preserves variable equality, rule
premises, and the same-variable fast path; induction maps every finite closure
step in both directions. This is a constraint-graph isomorphism for the
prepared view. It is not a denotational solution-set result: the draft has not
defined a subtype satisfaction relation for regular types.

**Structural use isolation.** For two distinct uses `u != v`, require their
fresh image sets to be disjoint and to intersect the stable graph only through
`E_d`. Every raw copied edge then mentions local IDs from at most one use, plus
stable environment IDs. Closure can combine constraints through a shared
environment row: for example, `a_u <: e` and `e <: b_v` can derive a cross-use
obligation `a_u <: b_v`. Every such cross-use derivation must pass through an
identity in `E_d`; disjoint fresh identities rule out any other shared pivot.
This is the intended environment interaction, but the precise effect on use
solution spaces is not established here. The claim is limited to raw edge
separation and the shared-pivot condition on closure derivations. A
solution-space product and principal-solution theorem require a denotational
subtype model and remain unproved.

These conditional lemmas do not close Gate C. The full obligation remains to
define and prove the soundness/principality theorem for the supported graph
class and envelope, show that Oracle root preparation yields a well-formed
`H_d` with the `Gen_d`, `Free_d`, `Erase_d`, and `Cycle_d` behavior above, and
complete the charter's independent semantic/specification review before Gate
D. Evidence-sensitive edge selection, root/epoch transitions, and recursive
projection remain unproved.

Monomorphization may later choose concrete values for overlay ports and
specialize the selected member graph through the same lookup. It must preserve
recursive edges and `E_d` identities. This draft does not specify a cache key,
runtime representation, or serialization format.

## 5. Candidate correctness statement

For a finite initial component graph `G₀`, member-specific boundaries and
environments `(B_d, E_d)`, ordered member roots `r₁ … rₘ`, and incoming uses
`u₁ … uₙ`, the intended theorem is:

1. each open internal reference resolves to the live SCC root and contributes
   the same constraints as the pre-quantification graph;
2. each ordered member step produces the same observable root result and
   leaves a successor state related to the Oracle state for preparing the next
   member, including root-local projection, prepasses, restarts, and bounded
   post-loop constraints; this relation need not identify internal graphs;
3. the collected root views become visible before any external incoming use;
4. each external use of member `d` receives fresh substitutions for `Gen_d` and
   the recursive identities in `Cycle_d`, while surviving `Free_d` variables
   retain their identity through `E_d` and `Erase_d` occurrences stay erased;
5. the overlay solver returns a principal solution for that use, and constraints
   from `uᵢ` cannot change the solution space of `uⱼ` for `i != j` except through
   identities explicitly shared by their environments;
6. cycles and shared descendants remain regular graph edges and do not require
   path duplication to state the result.

This statement is not yet a theorem: “equivalent”, “principal”, the exact
boundary-relevant port criterion, the state transition relation, and the
supported type constructor algebra need definitions. It deliberately says
nothing about matching F5 binder shape.

For the first graph comparison, “same observable constraints” means that after
applying each use overlay and closing subtype obligations, the positive and
negative bound reachability at that use and at every shared outer vertex is
isomorphic up to fresh internal vertex renaming. Agreement only after rendering
a formatted scheme is too weak: it could hide lost edges, merged independent
uses, or captured outer identity. This graph isomorphism is a proof aid, not a
proposed public scheme contract.

## 6. Required counterexamples and proof obligations

Before choosing a runtime representation, the proof must cover:

- a diamond with two paths to one local vertex, proving one port is shared;
- a local diamond ending at an outer rigid vertex, proving capture is avoided;
- a nested Function where the same vertex is exposed at both polarities,
  proving one parent identity while retaining both directional edge sets;
- two incoming uses constrained differently, proving overlay disjointness;
- an SCC with an internal reference plus an external incoming use;
- productive nominal-guarded recursive Function bounds, retaining all cycles;
- an unproductive Function-only cycle, matching its observed collapse;
- the Oracle's actual root-processing order, including a characterization of
  when swapping roots changes later views and when the steps commute;
- failure during preparation, proving no member is partially published.

The first essential lemma is a lossless boundary factorization: every
constraint path from a local SCC vertex to an independently instantiable
exposure crosses exactly the selected boundary ports, while paths to outer/
rigid vertices remain anchored in `E`. The second is overlay isolation. The
third is principal solving for the chosen finite regular graph class. None has
been proved here.

### Worked closure facts

**Identity root.** The body graph contains one `Function⁺` node whose argument
references `a` negatively and result references the same `a` positively. Its
lower edge into the definition root preserves this exact sharing. The Oracle
accepts `pub id x = x`; its two observed incoming uses produce `int` and a
Function result independently. This checks an acyclic boundary with one
bipolar vertex, but does not establish parent selection for recursive graphs.

**One-sided parameter.** The Oracle accepts `pub k x = 1` with scheme
`any -> int` and no quantified or recursive binders. Thus parent graph closure
alone cannot be the per-root result: the negative-only argument variable must
be projected away. The intrusion design needs a root projection that preserves
the component graph for other roots while eliminating this member's
one-sided exposure.

**Directed variable flow.** For `a⁺ <: b⁻`, closure stores `a⁺` in `lower(b)`
and `b⁻` in `upper(a)`. It does not assert `a = b`. A candidate that maps both
vertices to one parent would turn these obligations into self-edges and erase
the distinction. Unless a separate theorem justifies that quotient, the safe
candidate retains distinct ports and both directed bounds.

**Use separation.** Two identity uses create overlays `sigma₁` and `sigma₂`.
The observed Oracle program instantiates one at `int` and one at a Function
type. If both overlays wrote into one mutable component graph, either choice
could constrain the other use. The immutable graph plus disjoint overlays
avoids that direct mutation, but a proof must still show propagation cannot
escape from one overlay through a shared outer endpoint except where the
enclosing environment intentionally shares it.

## 7. Known gaps and next step

### Projection evidence and member-root preparation

The Rust implementation cannot treat an SCC as one global compact root. In
the frozen Oracle, each call to `compact_type_var_for_scheme` creates a fresh
projection-evaluation round, scoped query, and collector. During root
generalization, this compaction may be repeated after constraints change; the
Oracle caches the compact result by root and constraint epoch. Each attempt
then asks for lower records only as it reaches a variable from that root. The
round has preflight state, proof-evaluation memo, cycle handling, and a
terminal failure. This is per compaction attempt, not a claim that all work
for one root or SCC shares one immutable snapshot.

A source-compatible preparation operation must currently be specified as an
ordered root step over mutable solver state:

```text
prepare_member_step(state_i, member_root, environment):
    repeat:
        create projection round/query for this compaction attempt
        lazily visit (vertex, polarity, weight) in collector order
        on positive visits, query lower records by evidence lane, then ordinary lane
        if any projection query fails, return failure without a root result
        retain Unclaimed and Included; omit Excluded
        on negative visits, read upper records in the same lane order
        preserve recursion identity by (vertex, polarity)
        build this attempt's regular projected root and polarity census
        run prepasses required by the declared input envelope
        apply constraints participating in this root's restart loop
    until this root's Oracle restart condition is satisfied
    run bounded post-loop passes; apply their constraints without assuming restart
    save the root result produced here and return updated state (state_i_plus_1)
```

The component preparation result is staged privately. Any terminal projection
failure aborts preparation, produces no member view for that component, and
prevents partial publication. This is the replacement's atomicity rule; it does
not describe Oracle's sequential slot finalization.

`state_i` must eventually include every input that can affect a later root,
not only the bound graph: proof/projection state, relevant role or cast inputs,
already-applied constraint identities, and the enclosing environment. The
first theorem fragment uses pure inputs with no effects, rows, methods, roles,
or casts. It does not establish behavior for those features; expanding the
supported envelope requires adding their state transitions and proof
obligations. This staged proof does not narrow the overall replacement
objective.

The pseudo-operation describes a source-derived protocol, not the chosen
production representation. Each compaction attempt has its own selected
lower-edge occurrences; the root step may add constraints and restart before
the view is complete. A later parent renaming must transport each successful
attempt's graph without changing its selected edges; the renaming lemma applies
only after that selection step. A component-wide mask is an optimization
candidate only if it proves identical per-root, per-epoch decisions and
traversal-reachable failures.

Failure has multiple scopes in the Oracle. `project_lower` latches a failure
within its evaluation round, and the scoped query gateway can escalate certain
failures to an inference-attempt terminal failure. The surface wrapper maps a
returned query error to a default compact root, but this is not evidence that
the failed root view is semantically accepted. The replacement must define a
deterministic failure result and avoid publishing a partially prepared
component; that is a replacement safety requirement, not an assertion that
Oracle member-slot writes are atomic.

The Oracle scheduler invokes component quantification, but root generalization
is sequential and may add merge, subtype, cast, or role constraints and
restart. A later member root can therefore be compacted at a newer constraint
epoch. The replacement must specify its own freeze boundary and prove how it
simulates these root-specific prepasses and epoch changes; requiring every
member view to use one shared snapshot is a design candidate, not an observed
Oracle invariant. A selected-edge cache cannot outlive or detach from the
proof snapshot that validated it. Whether overlays may add constraints after
publication, and whether a later root projection must see those constraints,
remains part of the component denotation and is not settled here.

### Ordered root-step simulation obligation

The root-indexed statement in §5 is not proved by observing a two-root example.
A useful example can expose a missing case, but the Gate C proof must cover an
arbitrary finite ordered member list. Nor may the proof assume that bounded
post-loop constraints are denotationally redundant: applying them changes
canonical solver state and may route events or alter the evidence available to
a later projection. No such redundancy has been established.

For the declared graph envelope, define a checkable relation `R_i(O, I)` between
the Oracle state `O` and intrusion state `I` immediately before member `d_i`.
The relation is over current inputs rather than eventual outputs. At minimum it
must provide a transport map for source identities and require:

1. Enclosing identities in `E_d` map to the same anchors. Surviving local
   vertices map injectively to their live or parent representation, with
   current levels, birth levels, non-generic status, constructor shapes,
   polarity, weights, and both directed bound relations preserved under the
   map. The current member root, its `B_d` boundary and fetch mode, and the
   lookup correspondence for `E_d` are also related explicitly; matching the
   graph alone does not imply matching quantifier eligibility or root-local
   selection.
2. Reachable bound records have corresponding proof carriers and validity
   dependencies. Evidence-lane and ordinary-lane records remain distinguishable
   and ordered. Numeric IDs and internal graph node IDs need not match.
3. Pending subtype obligations, queued events, and the meaning of already
   applied constraint keys correspond. Epoch numbers need not be equal, but
   cache/proof validity and invalidation must correspond.
4. The next member and remaining member order agree. Previously saved member
   views are related as immutable observations; they are not required to equal
   a fresh projection of the current, later-mutated solver state.

`R_i` must not assume the projection decisions for every future root. That
would hide the evidence-sensitive selection problem inside the state invariant.
Prove a separate **projection congruence lemma**: related current inputs for a
given root yield corresponding ordered visits, evidence/ordinary record
queries, `Included`/`Unclaimed`/`Excluded` decisions, and corresponding query
outcomes. The outcome relation must distinguish a compaction-attempt-local
projection error, a round latch, escalation through the scoped query gateway
to an inference-attempt terminal latch, and the surface fallback that converts
a returned query error to a default compact root and continues. The proof must
classify errors reachable in the declared envelope, simulate the matching
continuation and downstream reporting, or prove a fallback path cannot affect
any public result. The transported selected constraints must preserve
polarized closure; proof-record identities may differ if their validity and
selection meaning are preserved.

Then prove a **whole root-step lemma**. Starting from `R_i(O, I)`, simulate the
complete Oracle preparation of `d_i`: each compaction attempt, restart,
prepass, alias expansion, stack cleanup, both bounded post-loop applications,
constraint-event routing, role prerequisites admitted by the envelope, and
the point where the saved member view is formed. On ordinary success, the
saved views must be equivalent under the transport map and the successor
states must satisfy `R_(i+1)`. On a returned query error, the lemma must
simulate the Oracle's actual latch or default-root continuation and resulting
diagnostics; it may require a terminal replacement result only when the
corresponding Oracle path is terminal. It must rule out extra successful
public results. The lemma must account for the
fact that the compact snapshot used to form a saved view can predate a
post-loop solver mutation.

Induction over the ordered member list then proves corresponding collected
views. A separate component-stage lemma must simulate all-member publication
and finalization: the Oracle finalizes only after collecting every root view,
and finalization reads the then-current shared solver state. Finally, induction
over incoming-use events must preserve member selection, per-use injective
freshening of `Gen_d ∪ Cycle_d`, stable `Free_d`/`E_d` anchors, `Erase_d`
projection, resulting obligations, diagnostics, and public type observations.
Uses may interact through shared environment identities; unconditional
solution-space product decomposition is not required.

This operational simulation would establish the declared observable parity
only after its observation relation and envelope are fixed. It does not prove
type soundness or principality. Those require a separate denotation of
polarized subtype constraints and a principal-solution preorder, followed by
proof that root projection and use overlays produce sound principal results.
The current injective-renaming lemma covers only closure after edge selection;
none of the projection, root-step, finalization, use, soundness, or principality
lemmas above is proved. A two-root graph-level characterization remains useful
as diagnostic evidence, but is not a substitute for these lemmas.

### Denotation boundary and unresolved choices

The closure operator in §1 is an operational propagation relation. It is not a
type satisfaction relation: proving that parent renaming commutes with closure
does not show that a graph has any valid solutions, that a projected view is
principal, or that the Oracle projection preserves solutions. Keep two proof
layers separate:

1. For an already selected regular member graph, define assignments to local
   vertices with enclosing identities held fixed, a satisfaction relation for
   every subtype obligation, and a preorder on solutions that makes
   “principal” precise. Prove soundness and principality of the proposed
   projection and per-use overlays under those definitions.
2. Prove that each Oracle root/epoch preparation corresponds to a selected
   graph in that model, including evidence-lane decisions, failures, root
   ordering, saved views, and use routing.

The required definitions are not recoverable from the existing closure rules
alone. A successor semantics still has to decide: (a) whether recursive types
are interpreted as equi-recursive regular trees or by another relation; (b)
how `Bottom`, `Top`, unions, intersections, Function variance, and nominal
constructors are interpreted; (c) what local vertices range over and how shared
environment anchors constrain assignments; (d) whether principality means a
most-general factorization, a least/greatest element in a subtype preorder, or
another property; and (e) how unguarded cycles and polarity-only recursive
collapse fit that interpretation. No option is selected here. Oracle's
evidence-sensitive lower-edge choice remains an operational refinement of the
selected graph, rather than an implicit clause of type satisfaction; its
correspondence still needs proof. The Oracle's `SchemeRecursiveBound` is a
side-table TypeVar plus neutral bounds, not a stated equi-recursive type
equality: each incoming use freshens the recursive variable, projects its
lower and upper bounds, and reinstalls them as subtype constraints. This
operational fact constrains the implementation comparison but does not choose
the denotational interpretation of recursive solutions.

This split follows the audited Oracle path: compaction creates a fresh
projection round, lower bounds are selected through a scoped evidence query,
and returned query errors can become a default root at the surface. Therefore
bare graph satisfaction cannot stand in for the round-local selection and
failure behavior.

These requirements expose two characterization targets before representation
selection: compare resulting member-root views, diagnostics, and incoming-use
behavior at the public solve boundary through executable runs of the actual
Oracle and candidate Rust solve paths; and characterize exact round-local edge
decisions through either a trace-capable Rust harness or a separate source
proof. Public results alone cannot expose query-round identity or selected-edge
masks. Rust applies to executable characterization; a source proof remains a
separate valid route for the edge-decision target. Neither route replaces the
soundness/principality proof gate. Previous finite Python-model results are
retired and must not be used as characterization or implementation evidence.

The Yulang2 audit found in-place level lowering in `extrude_pos` and
`extrude_neg`, not fresh parent allocation. Therefore this candidate cannot be
described as a proved optimization of that operation. It is a new semantics to
compare by observable behavior.

The Oracle source language probe for two mutually recursive local definitions
capturing one outer parameter failed on the forward local reference. That exact
topology therefore needs either a valid source construction or a synthetic
constraint-graph characterization with an explicit note that it is not a
source-level Oracle observation. Pure Function-only and nominal-guarded cycle
witnesses currently establish only their exact observed programs.

Next, define the polarized bound-graph denotation and principal-solution order,
then discharge projection congruence, whole root-step simulation, finalization,
and use-event simulation for the declared envelope. A two-root witness may
characterize a case, but the ordered simulation is the proof obligation.
Implementation and production representation remain gated on a reviewed
successor contract and explicit approval.
