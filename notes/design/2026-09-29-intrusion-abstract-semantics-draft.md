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
unfolding. The narrow graph fragment currently written below contains only
`Bottom`, `Top`, atomic constructors, variables, and polarized Functions.
Function arguments reverse polarity; results preserve it. It excludes effects,
rows, methods, role constraints, and handler hygiene. This is a graph-level
candidate only: source Function schemes also carry latent effect identities,
which can be forced and freshened even when the source has no explicit effect
syntax. Thus the fragment cannot yet claim source-level Oracle parity for the
Function fixtures.

The recorded source characterization programs use top-level `pub`
definitions, sequential local `my` bindings where name resolution succeeds,
mutually recursive top-level definitions, variables, integer literals,
single-parameter backslash lambdas, expression application, finite tuples,
records, and the unary nominal constructor `wrap` declared as
`struct wrap 'a { value: 'a }`. The identity/two-use, captured-diamond, pure
Function unproductive-cycle, and nominal-guarded two-member SCC with three
incoming uses are exact Oracle observations, but they do not all inhabit the
narrow graph fragment: the diamond needs tuple/record closure, the guarded SCC
needs nominal closure, and Function source observations need latent effect
behavior. They remain characterization fixtures, not evidence that the
fragment covers those cases. Annotations, imports, arbitrary nominal families,
explicit effects, handlers, stacks, rows, methods, variants, roles/casts, and
failed local forward references are outside this initial set of source probes;
the following candidate separately admits the exact annotations used by the
forced local effect-binder fixture.

Expanding the theorem to cover these source fixtures requires product subtype
rules for tuple arity and record fields, nominal constructor compatibility and
variance, a guardedness predicate with recursive interval-bound semantics, and
a model of the latent effect identities that affect Oracle observations. Those
rules and their closure/renaming lemmas are not specified here. The exact
source/event alphabet and public observation normalization also remain open.
Current Yulang3 HIR has no application node and rejects the identity witness's
lambda/application path, so its Rust path cannot yet establish source-level
parity. Graph-level characterization and source-level Oracle parity must be
reported separately until both a lowering bridge and the required semantic
extensions are defined and proved.

### Candidate end-to-end source envelope (unselected)

The effect-free graph above is only a possible lemma. The current Oracle
characterizations require a wider candidate envelope before an end-to-end
parity claim is meaningful:

- top-level `pub` definitions, resolvable sequential local `my` definitions,
  and mutually recursive top-level SCCs;
- variables, integer literals, one-parameter lambdas, and the multi-parameter
  definitions used by the observed fixtures, with expression application and
  the call shapes used to form and consume recursive members;
- the bounded annotation forms used by the forced local effect-binder fixture:
  an annotated outer definition with `l: int`, `sink: 'e -> int`, and result
  `int`. This annotated parent selects local reads that instantiate the saved
  scheme; without it the reads stay on the live value;
- finite tuples and the closed required-field records used by the witnesses;
- the observed unary invariant nominal constructors `wrap` and `loop`, with
  nominally guarded regular recursion;
- ordinary implicit Function/evaluation/result effect identities, effect
  bounds, forced effect quantification, and per-use freshening while preserving
  unquantified environment identities;
- per-member value/computation fetch boundaries, ordered root preparation,
  open internal uses, all-member publication, and independent incoming uses;
- public success/failure status, exported type observations, and ordered
  diagnostics with source locations and semantic payload.

This candidate covers the recorded identity/two-use, constant Function,
negative-argument projection, captured-diamond, nested/self and mutual
unproductive recursion, nominal-guarded Function SCC, anchored alias, forced
local effect-binder, and three-incoming-use characterizations. Those fixtures
do not establish the general rules. In particular, full record and tuple
subtyping, nominal guardedness, recursive interval semantics, latent-effect
algebra, forced-binder selection, ordered root simulation, transitive use
isolation, and public normalization remain to be defined and proved.

Explicit effect-row syntax, handlers/hygiene, imports, arbitrary nominal
families, rows, methods, variants, and roles are not represented by the current
fixture set. Their exclusion here is only a limit of this candidate gate; it
does not reduce the overall Oracle-capability objective. Any eventual
supported-input limit or observable compatibility delta requires its own
successor-contract review and approval. The candidate may be expanded as Oracle
evidence and the proof require; it is not yet a selected compatibility
boundary.

The graph has two kinds of identity:

- a **type vertex** identifies one shared unknown and owns its lower and upper
  bound edges;
- a **boundary port** identifies one independently substitutable exposure of
  that graph at a generalization boundary.

An edge occurrence records a polarized type endpoint, its direction, stable
source/proof identity, and any weight annotation. An endpoint is a constant, an
application of a constructor admitted by the selected graph fragment to
endpoints, a Function of endpoints, or a reference to a type vertex. A lower
edge records `endpoint <: vertex`; an upper edge records
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
upper-branch obligations. Mismatched constructors and all effect/row cases are
excluded from this first graph class.
This records the Oracle's operational constraint relation for the fragment,
not a denotational model of all possible runtime types. The source audit and
the SCC scheduling observations are recorded in the behavior ledger.

Outside that candidate fragment, the Oracle also decomposes equal nominal
constructor heads according to declared argument variance; the observed
`wrap` fixture uses an invariant argument. This is a source characterization,
not a rule currently covered by the candidate closure or renaming lemmas.

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
Lsrc_d = Local_d
Phi_d : Lsrc_d -> fresh member-owned ports
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
immutable selected input for that root attempt. The ordered root sequence may
advance the shared solver state between attempts; this does not posit one
immutable SCC-wide snapshot. Polarity census for one root must not absorb
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
- `Free_d`: resolve through the component-stable environment map `beta_C` to
  an anchor in `A_d`, then keep that anchor fixed.

No `Erase_d` variable occurs in `H_d`; its extreme node is copied as a
constructor leaf. This keeps erasure separate from the injective variable
renaming.

Constructor nodes and both edge directions are copied homomorphically. Stable
source/proof identities and edge order are retained; any type-variable
payload in evidence uses the same variable map. A source identity that belongs
to both `Gen_d` and `Cycle_d` is mapped once through `Phi_d`. The resulting
variable map must be injective over identities still present in `H_d`: distinct
local identities receive distinct fresh IDs, and all resolved environment
identities remain fixed. Fresh ranges must be disjoint from the entire
receiving identity namespace, including caller variables outside the view,
and from other uses' fresh ranges. A boundary collision is a view-construction
failure, not implicit capture.

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
prepared view. It does not by itself establish that the bound graph has
principal solutions.

**Conditional solution-set transport.** Fix any semantic carrier `D`, an
interpretation of graph endpoints into `D`, and a relation `≤` on `D`. For a
selected graph `G` with local vertices `L` and resolved anchor vertices
`A`, let `Sol_D(G, eta)` be the assignments `nu : L -> D` for which every
selected lower/upper obligation holds under `eta : A -> D`. This definition
does not choose `D`, endpoint interpretation, or `≤`; those are still an open
semantic decision.

Let `rho : L -> P` be a bijection to fresh identities, disjoint from the
entire receiving identity namespace, and the identity on resolved anchors `A`.
Rename every local variable occurrence in the selected graph
homomorphically, preserving constructors and edge direction. For each `nu`
define `rho_*(nu)(rho(v)) = nu(v)`. Then:

```text
nu in Sol_D(G, eta)  iff  rho_*(nu) in Sol_D(rho(G), eta)
```

For this lemma only, endpoint syntax is finite constructor syntax with every
cycle in the selected graph returning through a variable reference. Evaluation
of that reference is a direct lookup in `nu` or `eta`; it does not unfold the
variable's bound edges. Assume constructor interpretation respects this
evaluation rule. Structural induction over each finite endpoint then gives
`eval(rho(e), rho_*(nu), eta) = eval(e, nu, eta)`, so every selected subtype
obligation has the same truth value. Since `rho` is bijective on local
vertices and fixes `A`, `rho_*` has the inverse assignment map and gives a
bijection of solution sets. Root observations are preserved only when they
depend extensionally on interpreted root values, not on raw vertex IDs. If a
later model interprets recursive bounds by unfolding or a fixed-point
construction, it must separately prove renaming equivariance for that
interpretation. This conditional lemma does not show that `G` or its projected
view is principal, that the selected graph is Oracle-compatible, or that
one-sided erasure preserves the solution relation.

**Structural use isolation.** For two distinct uses `u != v`, require their
fresh image sets to be disjoint from one another and from the entire receiving
identity namespace. Every raw copied edge then mentions local IDs from at most
one use, plus resolved shared anchors. Closure can combine constraints through
a shared anchor row: for example, `a_u <: a` and `a <: b_v` can derive a
cross-use obligation `a_u <: b_v`. Every such cross-use derivation must pass
through an identity in the component anchor set `A_C`; disjoint fresh
identities rule out any other shared pivot. The copied use graphs may therefore
overlap through `A_C`, while no fresh identity intersects the stable graph.
This is the intended environment interaction, but the precise effect on use
solution spaces is not established here. The claim is limited to raw edge
separation and the shared-pivot condition on closure derivations. A
solution-space product and principal-solution theorem require a denotational
subtype model and remain unproved.

**Conditional joint-use renaming theorem (candidate).** Fix a many-sorted
identity signature `S` (at least value and latent-effect sorts), a carrier
interpretation for each sort, and subtype/effect relations for the corresponding
endpoint positions. An endpoint, assignment, constraint, and observation is
well-sorted; `rho` below is sort-preserving. A saved member view contains
finite regular endpoint terms, selected inequality obligations `C_d`, a typed
root observation tuple `R_d` (value root and any observable effect roots),
and preserved anchors `A_d`. Recursive bound rows are members of `C_d` as
inequalities; a variable back-edge evaluates by assignment lookup and is not a
recursive type equation. Fix a well-sorted shared assignment `eta_d` for all
identities in the receiver namespace, including anchors, with its admissibility
domain defined independently of whether the member-local fiber is empty.

For each incoming use `u` targeting `d`, let `L_d` be the complete set of
surviving member-local identities (ordinary, recursive, and forced-effect
identities), and choose a sort-preserving bijection `rho_u : L_d -> F_u`.
Require `F_u` to be disjoint from the entire receiver namespace and from every
other use range. `rho_u` fixes `A_d`; apply it consistently to root terms, both
sides of every inequality, effect positions, and all identity-bearing
constraint/evidence payloads. Assume endpoint evaluation and each
subtype/effect relation are equivariant under this renaming. This theorem
assumes each use view is a complete copy: every identity it reads is either in
`L_d` or the receiver namespace. Any omitted or erased identity must not be
read by the view, its continuation, or its observations.

Now choose an arbitrary finite, well-sorted joint continuation `W` over the
receiver namespace and the disjoint use-local copies. `W` may relate roots or
other observations from different uses, and may contain subtype/effect
obligations; it must be equivariant under the product renaming and fixed on
receiver identities. It may read only the identities just enumerated. For a
family of typed observations `z = (z_u)_u`, define:

```text
Batch_d(eta_d, W) = {
  z |
    there exist assignments nu_u : F_u -> D_sort for all u such that
      renamed C_d holds for each u under eta_d, nu_u,
      z_u = eval(renamed R_d, eta_d, nu_u) for every u, and
      W(z, eta_d, (nu_u)_u) holds
}
```

Here `D_sort` is the carrier selected by each identity's sort. The product of
the per-use assignment renamings is a bijection from assignments of the
original local identities, with one independent assignment per use, to
assignments of the fresh ranges. Structural induction on finite endpoint
syntax preserves each typed root value; each copied inequality and every
identity-bearing payload has the same identity correspondence. If payload
validity is part of the selected-view relation, its evaluator must also be
equivariant under `rho`; otherwise payload validity remains a separate edge-
selection obligation. Since `W` is equivariant, the full joint continuation
has the same truth value too.
Thus the complete batch observation relation is equal under the product
identity correspondence, including when `W` couples distinct uses. For every
fixed admissible `eta_d`, an empty original fiber maps to an empty renamed
fiber. Receiver assignments remain shared and may correlate uses; this
argument does not split them into per-use environments or assert that the
batch relation is a Cartesian product.

This conditional theorem assumes an already selected complete member view,
fixed sorted carrier interpretations, and semantic equivariance. It establishes
only identity-renaming transport for same-member use batches. It does not prove
that Oracle root projection selects `C_d`, that different member views compose
when an identity is free in one and local in another, that either scheme is
principal, or that the public Oracle observation is preserved. Those remain
separate Gate C obligations. The theorem also does not add handler hygiene: if
a later supported envelope admits handlers, their boundary identities and
evidence need a separate transport relation.

These conditional lemmas do not close Gate C. The full obligation remains to
define and prove the soundness/principality theorem for the supported graph
class and envelope, show that Oracle root preparation yields a well-formed
`H_d` with the `Gen_d`, `Free_d`, `Erase_d`, and `Cycle_d` behavior above, and
complete the charter's independent semantic/specification review before Gate
D. Evidence-sensitive edge selection, root/epoch transitions, and recursive
projection remain unproved.

Monomorphization may later choose concrete values for overlay ports and
specialize the selected member graph through the same lookup. It must preserve
recursive edges and resolved `A_C` identities. This draft does not specify a cache key,
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
one-sided exposure. A focused temporary test against the frozen Oracle now
inspects the first `compact_root_for_generalize` result for this source: the Function argument
contains `TypeVar(2)`, and `constraints().bounds().of(TypeVar(2))` is `None`.
The saved generalized compact root has an empty argument node, matching the
rendered `any` argument. This establishes the unconstrained-variable premise
for this one Oracle witness at the observed root-preparation point; it does not
establish the general root-projection rule or equivalence for bounded negative
variables.

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

The component preparation result is staged privately. A compaction-attempt
error is not automatically a component-terminal failure: the replacement must
simulate the Oracle's round latch, query-gateway escalation, or default-root
continuation for that error. When the corresponding Oracle path is terminal,
the replacement aborts preparation, produces no member view for that
component, and prevents partial publication. This is the replacement's
atomicity rule; it does not describe Oracle's sequential slot finalization.

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

**Unselected carrier option and review findings.** An architecture review
proposed using guarded regular type terms modulo alpha and equi-recursive
unfolding, with `Bottom`/`Top`, finite union/intersection, polarized Functions,
and invariant same-head nominal constructors. Local graph cycles would remain
inequalities over direct assignment lookup; they would not become recursive
type equations. This was only an option, and Oracle source inspection now rules
out importing equi-recursive comparison as an assumed subtype rule for the
frozen Oracle: its public polarity AST has no recursive type constructor,
and its subtype worklist compares finite shapes while variable cycles are
handled through bound propagation and deduplication. Recursive bounds are
recorded later as variable intervals during compact collection. This evidence
does not yet select a replacement denotation or prove that no mathematical
regular-tree model can characterize Oracle observations; it does require any
such model to prove observational correspondence rather than importing
coinductive/equi-recursive comparison as an assumed subtype law. Details and
scope are in `notes/progress/2026-09-30-intrusion-oracle-subtype-map.md`.

A compiler-referee review found a blocking gap for Gate C certification: the
option does not yet define a scheme's instantiation relation or prove that
projection/erasure yields exactly `Pred_d`. It also identified three major
proof obligations. First, the subtype preorder must say whether guarded
recursive comparisons admit cyclic/coinductive derivations; for example,
`X = μx.Arr(Int,x)` and `Y = μy.Arr(Int,y ∪ Int)` reduce to a repeated
`X ≤ Y ∪ Int` obligation after unfolding. Second, admissible environment
assignments must preserve empty fibers: `Int ≤ x ≤ e` has no solution when
`eta(e) = Bottom`. Third, inequality cycles must remain distinct from recursive
equations: `x ≤ Arr(Int,x)` admits `x = Bottom`, while
`x = μx.Arr(Int,x)` specifies a recursive value. The review did not find these
to be contradictions in the restricted finite fixed-endpoint lemmas; those
remain sound when the fiber is feasible and finite meets/joins exist. It found
that the option does not yet cover locally dependent constructor endpoints,
mixed-polarity roots, or Oracle root preparation and finalization. The full
findings and review limits are recorded in
`notes/progress/2026-09-30-intrusion-carrier-candidate-review.md`.

**Oracle ordinary use-instantiation operation (code characterization).** At
frozen Oracle revision `a58eefc31`, `infer::instantiate::SchemeInstantiator`
first allocates one fresh target variable for each ordinary quantifier and
recursive-bound variable, then clones the polarized predicate and recursive
bounds through a memoized source-variable/node map. Repeated occurrences of a
source variable in one invocation therefore share one target variable;
separate invocations use separate instantiators and fresh maps. Source
variables that are neither quantified nor already mapped are retained by the
ordinary internal adapter. Listed stack-subtraction IDs are freshened too;
otherwise-unmapped subtraction IDs are retained. Role predicates and function
effect positions are cloned through the same variable map, and stack weights
are cloned through a subtraction-ID map; stack quantifiers also add an outer
positive stack-pop wrapper. Recursive-bound intervals are reintroduced as
`lower ≤ fresh-var ≤ upper` constraints (`instantiate.rs`,
`instantiate_scheme_parts`, `fresh_var`, `clone_var`, and
`clone_recursive_bounds`, roughly lines 620–650, 720–750, 1002–1028).
At SCC use sites, `AnalysisSession::prepare_instantiated_use` clones at the
secondary level, then adds the instantiated positive predicate to the
use-value: constructor, Function, record, variant, tuple, and row roots take
the direct-lower path; other roots (including a bare variable) are related to
the use-value upper by a subtype constraint. Role predicates are installed separately
(`analysis/session/instantiate.rs`, roughly lines 344–365 and 448–535).
Imported/finalized schemes take a validated path that preloads session-owned
boundary variables; role-implementation candidate freshening is a separate
adapter with a different free-variable policy.

**One recursive inequality interval (Oracle characterization).** A temporary
Rust test against the same Oracle revision instantiated a scheme with interval
`Bottom ≤ q ≤ Arr(Int,q)`. Use emits no diagnostics; the fresh variable keeps
the self-referential Function upper, while the trivial `Bottom` lower is
discarded by constraint insertion. This is consistent with the candidate
inequality-cycle reading, but does not set `q = Arr(Int,q)`, compare recursive
types, or test a coinductive subtype rule. Exact assertions, reviewer scope,
and command are in
`notes/progress/2026-09-30-intrusion-recursive-inequality-oracle-probe.md`.
A second temporary Rust fixture gives the same fresh variable both lower and
upper bounds of the guarded `Arr(Int,q)` shape; Oracle retains both shapes
without diagnostics. This still does not choose a concrete solution or compare
distinct recursive schemes, so its scope is interval preservation only.

This is an operational characterization of the Oracle path, not a
mathematical scheme denotation. It does not specify the carrier/subtype
preorder, prove that a scheme's complete set of instances is principal, or
prove projection/erasure equality for intrusion. Imported-boundary and
freshen-all adapters have different free-variable policies; stack/effect
weights and role predicates also require their own transport account. These
details are evidence for the replacement's use-site simulation obligation,
not permission to copy F5's scheme architecture.

**Candidate principality criterion.** Once a carrier `D` and subtype preorder
`≤` have been fixed, a saved member view `H_d` induces the set of root types
realized by satisfying per-use local assignments. `H_d` contains source
TypeVar identities. Let `Free_d` be the source identities preserved across
uses targeting `d`, including outer/imported boundary identities, and let
`Lsrc_d = Gen_d ∪ Cycle_d` contain member-owned source identities freshened
per use. These sets must be disjoint, and every identity remaining in the
saved root or selected obligations belongs to `Free_d ∪ Lsrc_d`;
projected-away `Erase_d` identities do not occur in `H_d`. The component
resolver `beta_C : Free_C -> A_C` maps participating free source identities
injectively to stable anchors; `A_d` is its image on `Free_d`.
`Phi_d : Lsrc_d -> Ports_d` is an injective, member-owned source-to-port map.
For each use, `sigma_(d,u) : Ports_d -> Fresh_(d,u)` is injective, with fresh
ranges disjoint from the receiving identity namespace and all other use
ranges. Define `rho_(d,u)(v) = sigma_(d,u)(Phi_d(v))` for `v ∈ Lsrc_d`, and
`rho_(d,u)(v) = beta_C(v)` for `v ∈ Free_d`. Thus distinct surviving source
identities have distinct images. Write `eta_d : A_d -> D` and
`nu_u : Fresh_(d,u) -> D`.

```text
Root_d(eta_d) = {
    eval(rho(root_d), eta_d, nu)
    | rho is any valid use renaming of this member view, nu assigns its fresh
      range, and the renamed selected obligations of H_d hold under eta_d, nu
}
Pred_d(eta_d) = { T in D | exists t in Root_d(eta_d): t ≤ T }
```

**Environment-fiber convention (candidate clarification).** Let `Env_d` be
assignments to `A_d` satisfying the shared-only constraints for uses targeting
`d`; `Shared_d(eta_d)` means exactly `eta_d ∈ Env_d`. Shared-only constraints
include all relevant obligations whose resolved identities are all in `A_d`;
obligations involving fresh local identities remain in the member view. Do not restrict `Env_d` to
assignments for which the member has a local solution. For every
`eta_d ∈ Env_d`,
including one whose local fiber is empty, `Root_d(eta_d)` and
`Pred_d(eta_d)` are defined by the set comprehensions above; an empty fiber
therefore denotes the empty instantiation relation. A combined family of incoming uses has no
satisfying joint instance when any required use fiber is empty under the same
`eta_d`. This keeps infeasibility observable instead of repairing or dropping
it. The convention resolves the environment-domain ambiguity identified in
review, but does not choose `D`, `≤`, or the meaning of the Oracle's constraint
graph.

The upward closure is appropriate if the public typing relation admits
ordinary subsumption, where a root type may be used at any supertype; matching
that rule to the Oracle remains an obligation. A finite member scheme `S_d` is
principal under this candidate when its instantiation-and-subsumption relation
at every `eta_d ∈ Env_d` is exactly `Pred_d(eta_d)`. This states soundness and
completeness together, rather than
assuming that the projected graph is principal because it is finite. The
definition remains conditional: `D`, `≤`, `eval`, admissible environments, and
the denotation of scheme instantiation are not yet fixed, and it has not been
shown that a finite regular scheme can represent `Pred_d`.

For several incoming uses targeting the same member `d`, the environment
assignment `eta_d` is shared while each use gets an independent assignment to
its fresh local identities. Let `Use_u(t, eta_d)`
be the constraints and observations at incoming use `u` after receiving root
value `t`. The joint relation must retain the use-site obligations and root
results:

```text
exists eta_d ∈ Env_d .
  for every u, exists nu_u, t_u .
    nu_u assigns Fresh_(d,u) and
    Member(rho_(d,u)(H_d), eta_d, nu_u) and
    t_u = eval(rho_(d,u)(root_d), eta_d, nu_u) and
    Use_u(t_u, eta_d)
```

Each `nu_u` assigns that use's disjoint fresh identities. Every `Free_d`
source identity resolves through the same `beta_C` anchor and is assigned
through the shared `eta_d` at every use, matching
the Oracle behavior that retains unmapped free variables. When checking a
particular environment fiber, `eta_d` is fixed and its existential quantifier
is omitted. A single shared `eta_d` permits use constraints to interact through
preserved identities; distinct local assignments prevent direct local-variable
sharing. This matches the Oracle fixture where per-use binders freshen and
imported/free identities remain shared, but does not prove equality with that
fixture's use relation. `Member(rho_(d,u)(H_d), eta_d, nu_u)` abbreviates
satisfaction of every selected obligation in the renamed saved view under
those assignments. The `Root_d` set is independent of the chosen fresh IDs by
the conditional solution-set transport lemma. This formula covers a batch
targeting one member; different-member composition is
specified only by the following unselected candidate operation. One-sided erasure also remains open: the
observed `any -> int`
requires proving, under the chosen order and Function interpretation, that
replacing a negative-only local variable by `Top` preserves `Pred_d`; that
equality does not follow from closure or renaming transport.

The Oracle ledger gives concrete checks for this candidate, not proofs of it:
the identity root must retain one correlated argument/result assignment; the
constant-function root must satisfy the `Top` erasure equation above; imported
uses must choose independent Q/R assignments while sharing the imported B
anchor; and the guarded recursive Function fixture must be representable with
its recursive assignment fresh per use. A candidate carrier/order that fails
any of these observations cannot satisfy the Oracle target.

**Candidate graph-boundary instantiation operation (unselected).** This
operation keeps the generalized SCC and its member views as graphs; it does
not make a closed per-member type tree authoritative. Its precondition is that
ordered member preparation has produced valid saved views `H_d` and the
all-member visibility barrier has completed. For an incoming use `u` targeting
member `d`, first resolve each `Free_d` source identity through the stable
environment lookup `beta_C : Free_C -> A_C`; the member view uses its
restriction to `Free_d`, whose image is `A_d`. A source identity free in
multiple views maps to the same anchor. Distinct participating free source
identities must map to distinct anchors for this candidate's injective
transport argument; intentional aliasing needs a separate quotient proof.
Ordinary enclosing identities map to themselves; imported unit binders map
through the once-seeded unit boundary map. Use the member-owned map
`Phi_d : Lsrc_d -> Ports_d`, then choose an injective per-use map
`sigma_(d,u) : Ports_d -> Fresh_(d,u)`. Let
`A_C = union_d A_d` be all preserved anchors in the component. Fresh ranges
must be disjoint from the complete identity set `I_recv` in the receiving
solver graph and every incoming-use constraint, as well as pairwise disjoint
across all uses, including uses targeting different members. This includes
`A_C`, component source identities, and caller variables outside the
component. Thus if one source identity is local in one member view but free in
another, the first view receives a fresh identity and the second resolves it
to its preserved anchor. A globally fresh allocator is one way to enforce the
noncollision condition.

Apply `rho_(d,u)`—the composition of `Phi_d` and `sigma_(d,u)` on local source
identities and `beta_C` on free source identities—consistently to the view
root, selected edge endpoints, recursive-bound payloads, and every
type-variable occurrence in evidence/proof payloads. A proof carrier keyed to a renamed identity must itself
be transported with its validity dependencies or revalidated before use;
stable proof IDs alone do not establish that validity. Memoize cloned graph
nodes within one `(d,u,sigma_(d,u))` operation, never across uses. Add the
use's root constraint `Use_u` against that renamed root. Internal SCC
references during collection remain open live-root edges and do not pass
through this use operation.

For a batch targeting one member, the resulting constraint graph is the union
of the shared environment graph, each renamed view, and each use constraint.
For a batch targeting different members, apply each member's own identity
partition and renaming before taking the union over resolved shared anchors.
No component-wide quantification bit is used. The intended operational
relation is `G --Use(u,d)--> G'`, where
`G'` records the fresh map, renamed graph, root, and use constraint; a solver
then continues from that state according to the component driver's later
events. These events and their observation are defined by the candidate
relation below, not by treating each use as an isolated solver call.

Conditional solution semantics for `G'` quantify one assignment to each
preserved identity and a separate assignment to each use's fresh identities;
all copied edge obligations and use constraints must hold together. An empty
fiber stays empty. This transition can specify identity freshness, edge/root
transport, and use insertion without selecting a type carrier. Claims about
the set of possible root types, subsumption, soundness, or principality still
require an explicit carrier `D`, endpoint evaluation, subtype relation `≤`, and
an adequacy theorem connecting solver output to that relation.

The candidate's required proof obligations are: (i) each saved view is related
to the corresponding Oracle view at its actual ordered root epoch; (ii)
injective renaming preserves selected-constraint satisfaction and evidence
meaning; (iii) member-specific maps compose without capture when one source
identity is `Free` in one view and local in another; (iv) direct-lower and
general subtype use paths induce the same stated use observation; (v) empty
fibers and failures are preserved; and (vi) recursive bounds remain interval
inequalities rather than being silently converted into recursive equations.
The source `Free`/local partition coverage, cross-member batch relation,
public observation normalization, and carrier remain unproved. The contextual
observation function below is only a candidate proof interface. This operation
is a research candidate, not a selected representation or implementation
contract.

**Candidate contextual observation relation (unselected).** The quantification
domain is a canonical source program `P`, not a sequence containing solver
operations. For the current end-to-end envelope candidate, use this resolved
source grammar:

```text
Program ::= NominalDecl* Definition*
NominalDecl ::= WrapDecl | LoopDecl
WrapDecl ::= struct wrap 'a { value: 'a }
LoopDecl ::= struct loop 'a { next: 'a }
Definition ::= PubDef(site, name, params, result_annotation?, body)
             | MyDef(site, name, params, result_annotation?, body)
params ::= Parameter*
Parameter ::= Name(type_annotation?)
type_annotation ::= Int | FunctionType(TypeVariable, Int)
body ::= Expr
Expr ::= Name | Integer | Lambda(Parameter, Expr) | Apply(Expr, Expr)
       | Tuple(Expr+) | ClosedRecord((Label, Expr)+)
       | Nominal(wrap | loop, Expr) | Sequence(Expr+, Expr)
       | Let(MyDef+, Expr)
```

`site` is a machine-independent source path (module definition ordinal,
nested-definition path, expression child path, and annotation slot). It
identifies origins, not TypeVars, evidence records, or proof objects. A machine
may assign its own local subordinal to multiple constraints generated by one
site; that ordinal is not a shared identity. The lowering relation must relate
the generated obligations by their semantic roles without assuming the same
record count or order. The grammar is a resolved AST for the observed
fixtures, not a claim that current Yulang3 HIR already represents these forms.
`Sequence` preserves source evaluation order and effect accumulation. Type
annotations are limited to the exact integer and
`FunctionType(TypeVariable, Int)` forms used by the forced-effect fixture; the
annotation's type variable is distinct from latent effect identities created
by ordinary Function lowering. Tuple arity, closed record labels, nominal
variance, and expression typing remain semantic obligations rather than
parser commitments.

Each implementation lowers the same `P` independently:

```text
Lower_X(P) = (constraint_input_X, source_map_X, initial_errors_X)
```

The lowering relation must pair source origins by `site` while relating, not
identifying, their polarized endpoints, latent effect bounds, weight evidence,
and generated constraints. A site may lower to zero, one, or several machine
records; each source map can retain machine-local subordinals, while the proof
relates generated obligations semantically rather than pairing ordinals by
equality. Any source recovery or initial diagnostic is retained in the
lowering result. The proof must establish this relation for both Oracle and
intrusion paths, including the annotation-dependent choice between a live
local value and a saved local scheme.

Root attempts/restarts, incoming-use routes, and publication are generated by
the inference run and belong in `trace_X`, not in `P`. The traces record
constraint epochs, ordered member-root preparation, projection evidence,
internal live-root uses, post-publication instantiation uses, and the
all-member visibility barrier. Later constraints remain in the continuation
induced by `P`; they are not compressed into a single use batch. Finite trace
prefixes are used only in step-simulation lemmas and have no final public
observation.

Execution is split into an internal transition trace and a public observation:

```text
Run_X(state_X, Lower_X(P)) = (trace_X, public_X)
public_X = (status, ordered_diagnostics, exported_module_observations)
```

The internal trace records root attempts/restarts, projection decisions and
errors, round latches, query-gateway escalation, surface fallback to a default
root, constraint routing, use cloning/insertion, and publication. These are
not all public outcomes: an attempt-local error or round latch may be handled
by a later transition, and the surface may continue after a default-root
fallback. The public projection retains only what the Oracle exposes at the
end of `P`, including success/failure and ordered diagnostics with source
locations and semantic payload. Candidate diagnostic observations retain
normalized diagnostic code/severity, primary and secondary source locations,
and semantic payload in emitted order, subject to auditing which fields the
Oracle actually exposes. Exported observations are keyed by source definition
path and contain the public type/scheme result exposed for that definition.
Type-variable names and internal node IDs may be alpha-normalized if that
matches the public type surface. Anchor identity, polarity, recursive interval
bounds, and latent effect positions belong to the semantic root relation; they
are not assumed to be public fields. Whether public type equality follows the
Oracle formatter or equality of denoted principal solution sets remains
unresolved and must be fixed before claiming parity.

The candidate parity claim is that, for every pair of initial states related
by the root-indexed state invariant and every `P` in the supported source
grammar, Oracle and intrusion runs have the same
normalized `public_X` under one identity correspondence that fixes shared
anchors and consistently renames fresh local identities per use. Their
internal traces need not be equal; a root/use simulation relation must match
each public-relevant transition and continuation. This quantifies over
interleaved later constraints, root preparation, publication, and uses, not
only their immediate result at one use root. The root-indexed initial-state
invariant, source-lowering relation, effect/product/recursive interval
semantics, and public type normalization remain unresolved, so this is still a
proposed proof shape rather than a Gate C theorem.

For proof debugging, one may additionally record a non-public graph witness:
`BoundReach_X(P)` contains positive and negative bound reachability at
requested use roots and preserved outer anchors after the corresponding use
constraints. Comparing these witnesses under the identity correspondence may
expose a lost edge or captured anchor. It is optional diagnostic evidence,
not a parity requirement: graph isomorphism is not known to be necessary for
observational equivalence and would constrain the representation prematurely.

This relation is an operational comparison proposal, not a proof that the
candidate has a principal type. Matching possible root values for all
continuations, soundness, subsumption, or principality still requires a
carrier, endpoint interpretation, subtype preorder, and solver-adequacy
theorem. A candidate source grammar and lowering relation are now written, but
the source-to-AST correspondence, exact public type/diagnostic normalizer, and
simulation proof remain open; this relation cannot close Gate C.

**Unconstrained negative-parameter lemma.** A small erasure case follows from
the candidate relation. Assume `D` has a greatest element `Top` and a Function
constructor with the usual subtyping law:

```text
Arr(A, R) ≤ Arr(A', R')  iff  A' ≤ A and R ≤ R'
```

For fixed result `R` and an otherwise unconstrained local argument variable
`x`,

```text
↑{ Arr(A, R) | A in D } = ↑{ Arr(Top, R) }
```

For every `A`, `A ≤ Top`, so contravariance gives `Arr(Top, R) ≤ Arr(A, R)`;
therefore every member of the left generator set is in the right upward
closure. Conversely, assigning `x = Top` is allowed by the unconstrained
premise, so `Arr(Top, R)` is in the left generator set. Taking upward closures
proves equality. Thus the candidate principality criterion explains the
`Top` erasure of a truly unconstrained negative-only argument, such as the
observed shape `any -> int`. The focused Oracle probe above establishes that
the `k` argument has no stored bounds in the first prepared compact view and
that the saved compact argument is empty. If `x` has bounds, shares another
occurrence, or is anchored in `E_d`, this lemma does not apply; the general
`Erase_d` rule remains unproved.

**Bounded negative variable (conditional counterexample).** Polarity alone is
not enough to erase a negative-only variable. Assume a subtype preorder with
`Top ≰ Int` and the Function rule above, and let the local argument variable
`x` satisfy the selected upper-bound obligation `x ≤ Int`. The candidate root
relation is

```text
Pred = ↑{ Arr(A, R) | A ≤ Int }
```

but the polarity-only erasure relation is `↑{Arr(Top, R)}`. The latter
contains `Arr(Top, R)` by reflexivity. If that type belonged to `Pred`, some
`A ≤ Int` would satisfy `Arr(A, R) ≤ Arr(Top, R)`, which by contravariance
requires `Top ≤ A`; transitivity would imply `Top ≤ Int`, a contradiction.
Thus these relations differ. This is a counterexample in the candidate
denotation, not evidence that the Oracle emits this exact graph. A companion
source probe, `my expect(x: int): int = 1; pub k x = expect x`, observes a
bounded negative argument: its first compact view contains both the argument
variable and `Int`, the variable has an upper-bound record, and the saved
generalized compact root contains only `Int` in that argument position; the
saved public scheme is `int -> int` with no diagnostics. This is consistent
with the Oracle compactor expanding negative variables through upper bounds
before its one-polarity elimination pass
(`compact/collect/mod.rs::compact_var_side,compact_var_bounds`;
`compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic`).
It does not establish that this source graph is identical to the abstract
counterexample. An Oracle-equivalence proof must show how bound expansion and
evidence selection affect the saved root before applying any erasure argument.

**Pointwise extremal projection lemma (conditional).** Let `S ⊆ D` be the
nonempty set of admissible assignments to an argument variable after fixing
the result type and all other local/environment assignments. If `S` has a
greatest element `m`, then the Function rule gives

```text
↑{ Arr(a, R) | a ∈ S } = ↑{ Arr(m, R) }
```

For every `a ∈ S`, `a ≤ m`; contravariance gives
`Arr(m, R) ≤ Arr(a, R)`, so `↑{Arr(a, R)} ⊆ ↑{Arr(m, R)}`. Since `m ∈ S`,
the right generator occurs on the left, proving the reverse inclusion. A
preorder suffices. In particular, if `D` has finite meets and the constraints
on `x` are lower bounds `l_j ≤ x` and upper bounds `x ≤ u_i`, the admissible
set has greatest element `m = ∧_i u_i` whenever it is nonempty; for no upper
bounds, the empty meet is `Top`. Thus the `x ≤ Int` example projects to
`Arr(Int, R)`, not `Arr(Top, R)`, when `Int` is its greatest admissible
argument.

This is a fiberwise result only. It does not show that a variable has an
independent admissible set when it occurs elsewhere, that the extremum has a
finite representable graph expression when bounds depend on other variables,
or that the Oracle's evidence-selected root preparation produces the same
`m`. It therefore does not prove general `Erase_d`, principal solving, or
Oracle equivalence.

**Bounded interval projection lemma (conditional).** Fix the result type and
all other local and environment assignments. Assume `D` has finite meets and
the admissible assignments to a negative-only argument `x` are exactly the
nonempty set

```text
S = { a | for every j, L_j ≤ a, and for every i, a ≤ U_i }
```

where the endpoint values are fixed in this fiber. Let `m = ∧_i U_i`, using
`Top` for an empty upper-bound list. Any witness `a₀ ∈ S` gives
`L_j ≤ a₀ ≤ m` for every `j`, so `L_j ≤ m`; by the meet property `m ≤ U_i`
for every `i`. Thus `m ∈ S`, and every `a ∈ S` has `a ≤ m`. Therefore `m` is
the greatest element of `S`, and the pointwise extremal-projection lemma gives
`↑{Arr(a,R) | a ∈ S} = ↑{Arr(m,R)}`. This includes compatible lower
obligations; they establish that the upper-bound meet is admissible without
changing the greatest-element result.

This remains fiberwise and conditional on the exact definition of `S`.
It does not derive that set from Oracle evidence, cover endpoints that depend
on shared variables before fixing a fiber, or handle another occurrence of `x`
whose constraints couple the assignment to a different root position.

**Finite upper-graph projection (candidate denotation theorem).** Fix an outer
assignment. Let `V` be finite and let the selected obligations touching `V`
be a finite set consisting only of variable edges `u ≤ v`, fixed-endpoint
uppers `v ≤ U_i`, and fixed-endpoint lowers `L_j ≤ v`. Assume all remaining
obligations are independent of `V` and hold under the fixed outer assignment,
and that the selected graph has at least one satisfying assignment. The
carrier is a preorder with all finite meets, including nullary meet `Top`.
For each `v`, let `Reach_U(v)` contain every upper endpoint `U_i` reached from
`v` by zero or more variable edges, and set `M_v = ∧ Reach_U(v)`.

Every satisfying assignment `nu` obeys `nu(v) ≤ M_v`, since each reachable
upper is a transitive upper bound on `v`. If `u ≤ v` is an edge, then
`Reach_U(v) ⊆ Reach_U(u)`, hence `M_u ≤ M_v`. Each direct upper holds at
`M_v` by the meet property. For each direct lower `L ≤ v`, any satisfying
witness gives `L ≤ nu(v) ≤ M_v`, so the lower also holds at `M_v`. Therefore
the assignment `v ↦ M_v` satisfies the whole selected graph and is pointwise
greatest up to preorder equivalence, even when the variable graph has shared
vertices or cycles. In particular, `M_x` is the greatest feasible value of a
distinguished `x`. The feasible set for `x` need not be the whole lower set
below `M_x` when lower obligations exist; the greatest element is sufficient.

If the root is `Arr(x,R)`, `x` is its sole negative occurrence, and `R` is
fixed independently of `V`, Function contravariance yields
`↑{Arr(nu(x),R) | nu satisfies the selected graph} = ↑{Arr(M_x,R)}`. This is
a candidate denotation theorem for a finite pure variable-bound graph. It does
not show that Oracle selects the same obligations, that its replay reaches this
closure, or that concrete compact views preserve `M_x`; the existing Oracle
characterizations cover only the specific unweighted path and diamond fixtures
below.

**Finite lower-graph projection (candidate denotation theorem).** Fix an outer
assignment. Let `V` be finite, and suppose the selected obligations touching
`V` are only variable edges `u ≤ v`, fixed-endpoint lowers `L_j ≤ v`, and
fixed-endpoint uppers `v ≤ U_i`. Assume every remaining obligation is
independent of `V` and holds under the fixed outer assignment, and that the
selected graph has a satisfying assignment. The carrier is a preorder with
all finite joins, including nullary join `Bottom`. For each `v`, let
`Reach_L(v)` be the lower endpoints `L_j` whose owner is connected to `v` by
zero or more variable edges directed from owner to target, and set
`J_v = ⋁ Reach_L(v)`.

Every satisfying assignment `nu` obeys `J_v ≤ nu(v)`: each reachable lower
endpoint is a transitive lower bound on `v`, and finite join is its least
upper bound. If `u ≤ v` is an edge, `Reach_L(u) ⊆ Reach_L(v)`, hence
`J_u ≤ J_v`. Each direct lower holds at `J_v` by the join property. For each
direct upper `v ≤ U_i`, choose a satisfying witness `nu`; then
`J_v ≤ nu(v) ≤ U_i`, so the upper holds at `J_v`. Therefore `v ↦ J_v`
satisfies the whole selected graph and is pointwise least up to preorder
equivalence, including shared vertices and cycles. For a root consisting of
the positive variable `v`, `↑{nu(v) | nu satisfies the graph} = ↑{J_v}`.

This result concerns an already-selected finite bound graph. It does not say
that the compact collector selects these edges, nor does the positive-variable
corollary directly solve a Function root where one identity occurs both
positively and negatively: the argument and result fibers are coupled and
their extrema cannot be combined independently. The positive-result Oracle
source probe recorded in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`
motivates this dual graph lemma, but its recursive-call and latent-effect
constraints have not yet been shown to satisfy this theorem's complete
graph-class premises.

**Mixed-polarity source fixture relation (characterization only).** In the
positive-result fixture, write `x` for the shared Function argument/result
identity, `r` for the result root, `a,b` for the two local replay endpoints,
and hold outer `e` and `l` fixed. Abstracting only the five selected lower
records for `r` and four observed upper records for `x` gives this candidate
finite relation:

```text
x ≤ e       x ≤ a       x ≤ b       x ≤ r
a ≤ r       b ≤ r       x ≤ r       l ≤ r       int ≤ r
```

The repeated `x ≤ r` is one obligation. The source trace establishes the
record identities and empty weights, but those lower records are replay-
qualified, so treating the list as a complete selected graph remains a
conditional abstraction. For that abstraction, the root relation is the joint
image

```text
{ Arr(ν(x), ν(r)) | ν satisfies all listed edges, with e and l fixed }
```

under the same assignment `ν` at both occurrences of `x`. It is not the
Cartesian product of the argument and result projections: `x ≤ r` couples
them, while `l ≤ r` remains an environment anchor. Any candidate parent
transport must preserve this shared assignment and anchor. The trace and this
relation do not prove that Oracle finalization is denotationally equal to this
set, that the set has a principal regular Function representative, or that
parent intrusion preserves it through use and finalization. Establishing those
facts is the next proof obligation for this fixture.

For the abstract edge list alone, the existential local endpoints can be
eliminated exactly in any subtype preorder. A satisfying assignment implies
`x ≤ e`, `x ≤ r`, `l ≤ r`, and `int ≤ r` by the listed edges and transitivity.
Conversely, given these four inequalities, choose `a = b = x`; reflexivity
discharges `x ≤ a,b`, and `a,b ≤ r` follow from `x ≤ r`. Thus the projected
joint image is exactly

```text
{ Arr(x, r) | x ≤ e, x ≤ r, l ≤ r, int ≤ r }
```

with the same `x` in the Function argument and in the `x ≤ r` constraint.
This removes the auxiliary vertices without separating the shared polarity
fiber. It is a finite graph projection fact only; it does not identify this
relation with Oracle's saved scheme denotation.

**Oracle compact-root value projection (one source fixture).** A temporary
Rust-path probe now captures the actual post-generalization `CompactRoot` and
finalized local `Scheme` for the source above. The compact Function argument
contains the unweighted negative meet of `x,e,a,b,r` (TypeVars
`18,6,36,38,24`); its positive result contains the unweighted join of
`r,b,a,x,l,int` (TypeVars `24,38,36,18,2` plus `Int`). The finalized compact
root retains those meets/joins structurally. Under the preceding edge list,
`x` is a lower bound of every argument member and is itself a member, so the
argument meet is equivalent to `x`. Every result member is below `r`, and `r`
is itself a member, so the result join is equivalent to `r`. Thus the selected
value-position projection of this actual compact root agrees with the joint
graph image above, in any subtype preorder whose meet/join denote these
finite bounds. This is a conditional one-fixture correspondence, not a
principal-scheme or complete Function denotation theorem.

The full finalized Function also carries effects: the argument effect is
`Bottom`, and its result effect retains a primary variable plus eleven
secondary variables. This graph fragment does not model those effect
constraints. Generalization selects no ordinary quantifiers in this fixture;
the lowering path then adds one forced quantifier for the effect passthrough
(`TypeVar(21)`). It has no recursive bounds, role predicates, or stack
quantifiers. A focused test then instantiates this same finalized scheme twice
through Oracle's `instantiate_scheme`: each result-effect row preserves the
same eleven unquantified identities, while the forced TypeVar `21` maps to
distinct fresh variables (`TypeVar(0)` and `TypeVar(1)` in the target arena).
This characterizes the scheme-instantiation API's per-use map for this one
effect identity. A second source probe adds an `: int` annotation to the outer
binding and uses `inner l` twice after generalization. In this annotated-parent
path, both local references instantiate the saved scheme: the forced effect
identity becomes `TypeVar(45)` and `TypeVar(53)` respectively, while the other
eleven result-effect identities remain shared. This covers two independent
source-level incoming uses of a one-member recursive local component with the
same call shape. It does not cover differently constrained uses, multi-member
SCC publication/use scheduling, effect constraint denotation, or handler
hygiene. A separate pure source probe now covers one top-level, nominally
guarded two-member Function SCC. Oracle jointly quantifies both member roots;
both member schemes expose one shared quantifier vector while retaining
distinct recursive-bound roots. Two later source uses target `helper` with
`int` and identity-Function arguments, and a third targets `g` with an
identity-Function argument. Their use-value identities differ, the raw
TypeVar sets in immediate lower predicates are pairwise disjoint, and the
argument bounds retain the `Int` and identity-shaped Function lower forms. An
environment-gated production-instantiator trace reports three disjoint maps
for the component binder vector. The trace is sequential rather than keyed by
parent/target/use, and the test does not traverse transitive reachable bounds;
these are run observations, not a durable proof of complete map isolation.
This adds Oracle characterization for one multi-member publication/use path;
it does not establish candidate intrusion equivalence, principality, effect
constraint denotation, or handler hygiene. It is a top-level SCC witness and
does not resolve the separately failed local multi-member source construction
above. Without the outer annotation, the earlier one-member lowering path
instead keeps the live value when the forced quantifier is present. Exact
capture command and review scope are recorded in the progress note.

**Selected-edge fiber corollary (conditional).** The interval premise can be
derived for a restricted selected graph. Let `G` have a finite set of selected
variable subtype edges, interpreted as lower/upper obligations in a carrier
`D` with finite meets including the nullary meet `Top`. Fix an environment
assignment `eta` and assignments `nu_-x` to every other local vertex. Suppose
every selected edge mentioning local vertex `x` is exactly one of
`eval(l, eta, nu_-x) ≤ x` or `x ≤ eval(u, eta, nu_-x)`, and neither endpoint
depends on `x`; every other selected obligation is syntactically independent
of `x` and holds under `eta,nu_-x`. Then the satisfying fiber for `x` is exactly

```text
S_x(eta, nu_-x) = { a | every incident lower endpoint ≤ a,
                          and a ≤ every incident upper endpoint }
```

because these are all and only the selected obligations whose truth can vary
with `x`. If this fiber is nonempty, the bounded interval lemma gives its
greatest element as the meet of the evaluated upper endpoints, with `Top` for
no upper edges by the nullary-meet assumption. If the root is `Arr(x,R)` with
`R` independent of `x`, fixing
`eta,nu_-x` also fixes `R`, so its projected upward denotation is generated by
that meet. Environment vertices stay fixed by `eta`; this corollary does not
freshen or capture them.

This is a statement about an already selected edge graph. It does not prove
that Oracle's scoped evidence query selects exactly those edges, that compact
upper-bound collection retains their meet at the saved root, or that the
fiberwise extrema combine into a finite principal member view as
`nu_-x` varies.

**Acyclic upper-alias chain projection (conditional).** Extend the selected
graph fragment with local vertices `x = v_0, v_1, ..., v_n` and fixed endpoint
`U`, where the only selected obligations involving these vertices are
`v_0 ≤ v_1 ≤ ... ≤ v_n ≤ U`. Fix the result `R` and all environment values;
fix a satisfying assignment to every other local vertex; and assume every
remaining obligation is independent of these vertices and holds under those
fixed assignments. The feasible projection onto `x` is exactly
`{a | a ≤ U}`. Necessity follows by transitivity. For every `a ≤ U`, assigning
each intermediate vertex `v_i = U` satisfies the chain, proving sufficiency.
Thus `U` is the greatest projected argument, and the negative-only root
`Arr(x,R)` has upward denotation `↑{Arr(U,R)}` by the pointwise
extremal-projection lemma. This covers an acyclic alias path to a fixed upper
endpoint in the selected-graph model, not arbitrary shared intermediates,
weights, cycles, anchors, or constraints coupling any `v_i` to other local
vertices.

**Oracle correspondence for one unweighted alias chain (characterized).** The
frozen Rust solver has a replay path that materializes the chain's transitive
upper endpoint before generalization. Decomposing `x ≤ y` records `x` as a
projection lower of `y` and `y` as an upper of `x`. Inserting `y ≤ U` triggers
upper-bound replay at `y`, pairing its projection lower `x` with the new upper
`U` and queuing `x ≤ U`. A focused synthetic Rust-path test checks that `x`
then has a direct projected upper `U` and that full generalization of a
positive Function root with negative-only argument `x` drops the eligible
`x`/`y` occurrences while retaining exactly `U` in that argument position.
This matches the selected-graph chain projection for this unweighted,
acyclic, isolated chain and the tested level arrangement. The ordinary compact
collector itself retains a bare variable upper alias as a secondary
occurrence; the correspondence here depends on solver replay, not recursive
alias expansion by the collector. It remains a synthetic characterization,
not proof of source-level reachability, weighted/shared/cyclic path handling,
root-order simulation, diagnostics, or principal-solution equivalence for a
larger graph class. Exact source path and test command are recorded in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.

**One unweighted variable-alias cycle (bounded output characterization).**
For `x ≤ y`, `y ≤ x`, and `y ≤ U`, feasibility makes `x` and `y`
equivalent under the subtype preorder, and the projection onto `x` is
`{a | a ≤ U}`. A focused synthetic Oracle Rust-path probe places `x` as the
sole negative argument of an acyclic Function root and observes the finalized
argument `Con(U)`. This characterizes that two-variable alias cycle's output;
the cycle contains no Function structure and therefore says nothing about
productive recursive Function SCCs. Scoped record identity and broader cyclic
graphs remain open. Probe details and review scope are recorded in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.

**One anchored alias cycle with a compatible outer lower (synthetic Oracle
characterization).** The selected constraints are `l ≤ e`, `l ≤ x`,
`x ≤ y`, `y ≤ x`, and `y ≤ e`, where `l` and `e` are fixed outer identities
and `l ≤ e` holds in the chosen environment fiber. The selected-graph
projection onto `x` has greatest value `e`: every solution has `x ≤ e`, and
the assignment `x = y = e` satisfies the local edges. A focused frozen Rust
probe confirms one successful scheme projection query selects the exact lower
endpoint record `l ≤ x` and exposes upper endpoint `e`; propagation lowers
`x` and `y` to the outer level. The compact negative Function argument and
finalized root retain `x`, `y`, and `e` as free identities, with no local
quantifiers; `l` does not occur in that negative argument. This records the
Oracle's retained graph view, not a claim that the lower endpoint is
transported into the argument or causes retention of `e`. It is synthetic,
not a source-level witness, and does not prove parent/provenance transport,
later-root stability, or a general anchored projection rule. The focused test,
review scope, and source locators are in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.

**Two independent alias paths to an upper meet (conditional; one Oracle
characterization).** Let each path `j` have only the obligations
`x = v_{j,0} ≤ v_{j,1} ≤ ... ≤ v_{j,n_j} ≤ U_j`; intermediate vertices from
different paths are distinct and have no other incident obligations. Fix the
result `R`, the endpoints `U_j`, and a satisfying assignment to all other
locals; all remaining obligations are independent of the path vertices and
hold under those assignments. The feasible projection onto `x` is exactly
`{a | a ≤ U_j for every j}`: transitivity proves necessity, and assigning
every intermediate on path `j` to `U_j` proves sufficiency. If the carrier has
the finite meet `M = ∧_j U_j`, then `M` is the greatest feasible value and the
negative-only root projects to `Arr(M,R)`.

A focused synthetic Oracle Rust-path test characterizes two length-two paths
`x ≤ y ≤ U1` and `x ≤ z ≤ U2` with empty weights and eligible local levels.
Upper-bound replay inserts direct projected upper records `x ≤ U1` and
`x ≤ U2`; generalization removes the negative-only local variables, and
finalization produces a Function argument whose negative type is exactly the
intersection of the two concrete constructors. The tested compact and
finalized views therefore match the candidate meet projection for this graph.
This is not a source-language witness or proof for arbitrary path lengths,
shared intermediates, weights, cycles, environment anchors, later roots, or
principal-solution equivalence over a broader input class. See the focused
command, reviewer scope, and locators in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.

**One shared-join diamond (bounded output characterization).** For the
selected graph `x ≤ left`, `x ≤ right`, `left ≤ join`, `right ≤ join`, and
`join ≤ U`, the feasible projection onto `x` is exactly `{a | a ≤ U}`. The
upper bound follows by transitivity; conversely, any `a ≤ U` extends to a
satisfying assignment by setting `left = right = join = U`. A focused
synthetic Oracle Rust-path test with empty weights and eligible local levels
observes the same finalized negative Function argument `Con(U)`. The test
establishes this output for the diamond input, not that both replay paths or
the shared `join` identity survive as separate provenance in the projected
view; either route alone could induce the same final output. This is not a
general shared-DAG, weighted/cyclic, source-reachability, diagnostic, or
principality result. The probe and its reviewer scope are recorded in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.

**Restricted singleton-root path correspondence (conditional).** Consider a
pure acyclic member with structural Function root `Arr(x, R)`, where `x` is
the sole negative argument occurrence and has no other occurrence affecting
its polarity census, roles, or recursive sides. In the final projection
iteration, assume the per-root query succeeds and any required restart reaches
a state where `compact_var_side(x, negative)` has exactly one effective bound
input: one projection upper record compacted directly to a concrete atom `U`,
with no weighted alias, row, recursive, or secondary contribution. The
collector's complete argument side is the merge of the `x` occurrence and
that `U`; do not assume its pre-elimination compact form is just `x`.
Assume `x` meets the actual one-polarity elimination checks, including
`level_of(x) >= simplification_boundary`, `!non_generic(x)`, and a non-bipolar
occurrence census. Require the complete retained argument after merging the
self variable and this projection input and eliminating `x` to denote exactly
`U`; subsequent coalescing, ancestor simplification, and post-loop passes must
preserve that argument and `R`. Separately stipulate that the candidate's exact
admissible assignment fiber is the nonempty set `{ A | A ≤ U }`, with greatest
element `U`. Then the Oracle saved root denotes `Arr(U,R)`, while the candidate
fiber has upward denotation `↑{Arr(A,R) | A ≤ U} = ↑{Arr(U,R)}` by the
pointwise extremal-projection lemma. Thus their interpreted root denotations
agree for this restricted graph class.

The premises are substantive. The exact admissible fiber is a denotational
assumption, not a consequence proved by the presence of one Oracle upper
record; lower obligations, anchors, or correlations with other occurrences
can change that set. The observed `expect`/`k` source program is a concrete
`U = Int` path consistent with this theorem, but does not establish all its
premises or the general projection rule. This conditional correspondence does
not establish diagnostics, later-member state, incoming-use simulation, or
Gate C.

**Concrete source path for the `expect`/`k` observation (fixture only).** In
the frozen Oracle, lowering `expect`'s annotated parameter routes through
`connect_parameter_computation_detailed` to `connect_value_detailed`. For the
`int` annotation, the latter inserts both `Int <: expect_param` and
`expect_param <: Int`. Lowering `expect x` creates an application constraint
`expect_value <: Arr(k_arg, result)`; decomposing Function subtyping enqueues
the contravariant argument obligation `expect_param_inst <: k_arg`. Scheme
instantiation clones the finalized global scheme and submits its predicate by
the direct-lower or routed-subtype path. Thus, conditional on the finalized
scheme retaining the annotated argument relation, these source constraints
derive `k_arg <: Int`. The isolated Oracle Rust-path probe supplies the
remaining observed facts for this one fixture: the first compact view contains
the argument variable with an upper-bound record and `Int`, and the saved root
contains only `Int` in that position. This closes the concrete `U = Int`
source-construction example by combining source tracing with that probe; it
does not prove the premise for all finalized schemes, identify the exact
scoped query edge without the probe, establish saved-root stability for other
fixtures, or generalize to multiple bounds, aliases, anchors, and shared
occurrences.

The Oracle half follows this audited Rust path under those premises. In
`CompactBoundMode::SchemeProjection` with negative polarity,
`compact_var_bounds` reads the scoped view's generalized projection upper
records and folds each compacted bound with `merge_types(false, ...)`; direct
concrete constructors take the ordinary constructor-compaction path. Then
`compact_var_side` merges the source variable occurrence with that result using
negative intersection polarity. The one-polarity simplifier drops `x` only
when the boundary/non-generic checks pass and the root, recursive-bound, and
role occurrence census is not bipolar; `rewrite_type_vars` implements that
`None` result by removing the occurrence. With the stipulated sole concrete
input `U`, the retained negative argument is therefore `U`. Function
finalization sends that argument through
`finalize_neg_type`/`intersection_neg`, preserving the singleton `U`.
Relevant frozen-source locators are `compact/collect/mod.rs::compact_var_bounds,
compact_upper_bound,compact_var_side`,
`compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic`,
`compact/analysis/occurrence/substitution.rs::rewrite_type_vars`, and
`compact/finalize.rs::finalize_pos_fun,finalize_neg_type,intersection_neg`.
This path derivation does not prove that a given source program yields the
stipulated scoped upper record or that later root steps preserve it; those stay
explicit premises.

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

A later isolated Rust-path source probe does establish a narrower source
reachability fact:

```yulang
my outer(l: int, sink: 'e -> int) =
  my inner(x, y) =
    sink x
    inner y x
    inner l y
    1
  inner
```

The first post-lowering probe was misread: an `x` lower endpoint `y` and a `y`
upper endpoint `x` are two views of the same inequality `y ≤ x`, so this source
does not establish an alias cycle. An initial auxiliary query immediately
before `inner`'s generalizer selected lower records `y ≤ x`, `l ≤ x`, and
`int ≤ x` for `x`; this was not the generalizer's own query. Instrumenting the
actual compact collector showed that `x` and `y` occur in negative polarity
inside `inner`'s Function arguments. It therefore reads upper records `x ≤ e`,
`y ≤ x`, and `y ≤ e`, but makes no lower-projection query for either argument
at this root. The saved compact arguments contain `x` with `e`, then `y` with
`x` and `e`; the enclosing lower `l ≤ x` does not enter this member root.
Witness capture records the `x ≤ e` upper at the FunctionArgument
path, not lower record `l ≤ x`. The later lower-query trace is consistent with
the enclosing `outer` generalization, though the trace does not tag each
collector call with its root. This source probe therefore demonstrates why
syntactic solver reachability alone does not establish selected-edge
transport. The single local recursive member is not the failed multi-member
local-SCC construction above.

A second source variant reaches an outer lower in positive result polarity:

```yulang
my outer(l: int, sink: 'e -> int) =
  my inner(x) =
    sink x
    inner l
    x
  inner
```

The actual compact collector queried the Function result variable in positive
polarity and read replay-qualified lower records for `x`, the source `l`, and
`int`. Its compact result retained the outer `TypeVar` and `Int`. This is one
source-to-Oracle-view fixture, not an intrusion-equivalence or principality
proof. The lower evidence does not appear in generalized-witness capture
because the current top-level Function path records only the root argument.
Both examples have one recursive local Function and neither resolves the
failed multi-member local-SCC construction above. See
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md` for
captured record IDs, commands, and limitations. The earlier committed
source-probe note incorrectly called two views opposite alias directions;
the progress record explicitly corrects that reading.

Next, define the polarized bound-graph denotation and principal-solution order,
then discharge projection congruence, whole root-step simulation, finalization,
and use-event simulation for the declared envelope. A two-root witness may
characterize a case, but the ordered simulation is the proof obligation.
Implementation and production representation remain gated on a reviewed
successor contract and explicit approval.
