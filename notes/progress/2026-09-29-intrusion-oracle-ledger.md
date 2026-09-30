# Intrusion redesign: initial Oracle behavior ledger

Date: 2026-09-29
Oracle revision: frozen `main` at `a58eefc3`
Status: partial source audit with temporary probes executed; no Oracle source or test was committed

This ledger records directly observed Yulang2 behavior for the new SCC
intrusion design. It does not use F5 closed schemes as the target. Test
assertions below were read from the frozen source; no suite was run in this
research step. “Observed” means stated by source/test construction, not an
independently reproduced execution.

## Observed behavior

| Topic | Frozen-source observation | Evidence |
|---|---|---|
| Bound insertion / extrusion | Lower and upper bound insertion call `extrude_pos` / `extrude_neg` at the target/source level. `extrude_type_var` lowers the existing variable in place and traverses its installed lower and upper bounds with a visited set. Function argument positions traverse negatively and results positively. This implementation does not allocate a fresh parent representative. | `crates/infer/src/constraints/machine/bounds.rs`: insertion around 645/830; traversal around 4523–4727. |
| Definition SCC generalization | `quantify_component` creates a generalized result for each `(DefId, root)` member, collects all results, inserts all schemes, then processes finalization/recording. Incoming uses are not admitted inside the member-draft loop shown here. | `crates/infer/src/analysis/session/instantiate.rs:14–89`. |
| Identity Function boundary | The unit helper encodes an identity lower bound as `Fun(arg = -inner, result = +inner)` with pure Bottom effects. Under `FetchValue`, the fixture asserts the inner variable is quantified. Under `FetchComputation`, the same shape asserts no quantifier because the root remains at the binding boundary. | `crates/infer/src/analysis/tests/case_03.rs:338–371,1770–1787`. |
| Fresh use level | A manually built scheme with one quantifier is instantiated into a use value at root level; the test asserts the fresh variable is distinct from the scheme binder and is allocated at the use's root level. | `crates/infer/src/analysis/tests/case_02.rs::instantiate_use_freshens_quantifiers_at_secondary_level` (`:78–128`). |
| Recursive bound restoration | A manually built scheme with a recursive lower `int` bound is instantiated; the test finds a fresh variable on the use path and asserts that `int` is restored as its lower bound. | `crates/infer/src/analysis/tests/case_02.rs::instantiate_use_restores_recursive_bounds_for_fresh_quantifier` (`:219–281`). |
| Naked variable generalization | A child-level naked variable is generalized/finalized to an empty compact root and `Bottom` predicate, with no quantifiers. | `crates/infer/src/generalize/tests.rs::finalized_generalized_naked_root_variable_becomes_never` (near `:800`). |
| Recursive bound observation | A recursive interval containing `self ∪ int` is finalized with one recursive scheme bound whose lower side still contains `int`. | `crates/infer/src/generalize/tests.rs::finalized_generalized_root_moves_recursive_bounds_into_scheme` (`:834–861`). |
| Independent uses and shared outer identity | One manually constructed imported scheme is instantiated twice. The test asserts distinct fresh Q and R variables for each use while both uses map the same outer boundary variable to one session-level imported identity. | `crates/infer/src/analysis/tests/case_02.rs::oracle_a1_stage_3_exit_preserves_q_r_and_b_lifetimes_across_imported_uses` (`:494–598`). |
| Internal use while an SCC is open | A use whose source and target are already in the same open component is retained as an internal use. Once the target root is known, the use is constrained directly against that live root; if the root is not known yet, the use remains pending until registration. It is not sent through scheme instantiation while the component is open. | `crates/infer/src/scc.rs::add_use` (same-component branch); `crates/infer/src/scc/graph.rs::add_internal_use,open_pending_uses_for`; `crates/infer/src/analysis/tests/case_01.rs::open_scc_use_adds_target_to_use_constraint`. |
| Cross-component dependency barrier | An open dependency edge from one component to another blocks readiness of the source component. When a target component becomes ready, it is quantified and removed; its incoming uses then become `InstantiateUse` events, and predecessors are reconsidered. Thus the source use switches from a live open root to a use-site scheme instantiation only after target quantification. | `crates/infer/src/scc/graph.rs::is_ready_to_quantify,remove_ready_component`; `crates/infer/src/scc.rs::settle_components`. |
| Component publication | The scheduler's `QuantifyComponent` event carries aligned member and root vectors. The analysis handler generates a result per member, inserts all member schemes before finalizing any member into the poly arena, then finalizes them. This gives an all-member visibility barrier; it does not establish a shared SCC scheme representation. | `crates/infer/src/scc.rs::settle_components`; `crates/infer/src/analysis/session/instantiate.rs::quantify_component`; fixture `crates/infer/src/analysis/tests/case_01.rs::quantify_component_writes_scheme_to_poly_def`. |
| Source-level independent polymorphic uses | A temporary test against frozen `main` lowered `pub id x = x`, `pub number = id 1`, and `pub function_value = id (\\x -> x)` with no diagnostics. The resulting schemes formatted as `id: 'a -> 'a`, `number: int`, and `function_value: 'a -> 'a`. This observes one binding instantiated at both an integer and a Function type. | Probe command: `cargo test -p infer scratch_oracle_identity_independent_type_uses -- --nocapture` in a detached worktree at `a58eefc3`; source and output are captured in this row. Probe code was temporary and is not part of the Oracle commit. |
| One-sided Function parameter | The source `pub k x = 1` succeeds with scheme `any -> int`, zero ordinary quantifiers, and zero recursive bounds. The unused argument's negative-only type variable is projected away rather than retained as a polymorphic binder. A full-interval parent transport therefore needs a root projection/elimination step to match the Oracle even if edge transport itself is lossless. | Probe: `scratch_oracle_constant_function_one_sided_argument` in a detached `main` worktree at `a58eefc3`; inspected the scheme and binder counts. Temporary probe source was removed. |
| Prepared graph for one-sided Function parameter | In a temporary test against frozen `a58eefc3`, the first `compact_root_for_generalize` view for `pub k x = 1` contains a negative-only Function argument `TypeVar(2)` for which `constraints().bounds().of(TypeVar(2))` is `None`; the saved generalized compact root has an empty argument node. This directly establishes the unconstrained premise for the `k` witness, but not the general erasure rule. | `cargo test -p infer scratch_oracle_constant_function_prepared_graph -- --nocapture` in `/tmp/yulang-intrusion-constant-graph-probe`; one focused test passed. Temporary test and instrumentation were removed after the probe. |
| Root-local polarity projection path | Oracle scheme projection starts each member root at positive polarity, expands a variable through lower bounds at positive polarity and upper bounds at negative polarity, caches by `(TypeVar, polarity, weight)`, and detects recursive re-entry by `(TypeVar, polarity)`. After building the compact regular root, simplification collects polarities across the root and recursive-bound table and erases eligible one-sided variables; bipolar occurrences keep the same variable identity. The exact erasure candidate predicate is `level >= boundary && !non_generic`. For a parent-renaming proof, preserve that predicate and weight annotations; numeric level values need not be identical when a child-level variable is raised to the boundary. This is source behavior, not a required representation for the replacement engine. | `crates/infer/src/compact/collect/mod.rs::compact_root_for_scheme,compact_var_side,compact_var_bounds`; `crates/infer/src/compact/analysis/occurrence/mod.rs::collect_var_polarities`; `crates/infer/src/compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic,is_simplification_candidate`. |
| Source-level mutual recursive definitions | A temporary public-surface probe for `pub f x = g x; pub g x = f x; pub number = f 1; pub function_value = g (\\z -> z)` completed with no lowering diagnostics. Both member schemes formatted as `any -> never`; both incoming use schemes formatted as `never`. This is an observed result for this unproductive call cycle, not evidence about every guarded/productive SCC shape. | Probe command: `cargo test -p infer scratch_oracle_mutual_scc_independent_incoming_uses -- --nocapture` in a detached worktree at `a58eefc3`; probe code was temporary and is not part of the Oracle commit. The existing committed scheduler fixture `crates/infer/src/lowering/tests/case_06.rs::body_lowering_keeps_forward_cycle_in_one_scc` independently asserts that `my a = b; my b = a` merges and quantifies one component. |
| Nested self-recursive lambda source | The accepted source `pub f = \\x -> \\y -> f` formats as `any -> never` in the Oracle. This pure Function-only shape does not retain a recursive scheme bound; it differs from the nominal-guarded mutual Function SCC recorded below. | Probe command: `cargo test -p infer scratch_oracle_guarded_recursive_function_scheme -- --nocapture` in a detached worktree at `a58eefc3`; temporary probe code removed with that worktree. |
| Source-level recursive nominal and Function roots | A source-level self-recursive nominal value `struct loop 'a { next: 'a }; pub helper = loop { next: helper }` is accepted with scheme `loop 'a`, zero ordinary quantifiers, and one `recursive_bounds` entry. A recursive Function binding `pub helper x = loop { next: helper x }` is accepted with scheme `any -> loop 'a`, one ordinary quantifier, and no `recursive_bounds`. Thus the Oracle demonstrably supports guarded recursive type bounds in general, while this Function-valued witness does not create an R binder. | Probe command: `cargo test -p infer scratch_oracle_recursive_function_bounds_from_source -- --nocapture` in a detached worktree at `a58eefc3`. Probe inspected formatted scheme, `quantifiers.len()`, and `recursive_bounds.len()` for each source. Temporary probe code was removed. |
| Guarded mutual Function SCC with recursive bounds | The source `struct loop 'a { next: 'a }; pub helper x = loop { next: \\y -> g x }; pub g x = loop { next: \\y -> helper x }` succeeds without diagnostics. Both member schemes format as `any -> loop 'a`, each with 2 ordinary quantifiers and 1 recursive bound. Each recursive lower interval is a union of a variable and a Function whose result is `loop` with a recursive argument bound; the two bounds' upper sides point to the opposite member's recursive variable. This is an actual source-level SCC witness combining Function structure, nominal guarding, cross-member recursion, and R bounds. | Probe command: `cargo test -p infer scratch_oracle_recursive_function_shape_matrix -- --nocapture` in a detached worktree at `a58eefc3`; the probe inspected both members' scheme binder counts and recursive-bound graph nodes. Probe source was temporary and removed after the run. |
| Local diamond and captured rigid endpoint | The source `my outer x = my inner y = ({left: x, right: x}, y); inner` succeeds without diagnostics. The local scheme is `'a -> ({left: 'b, right: 'b}, 'a)` with one quantifier; the outer scheme is `'a -> 'b -> ({left: 'a, right: 'a}, 'b)` with two. Raw arena checks confirm both local record paths and the outer input use the same `TypeVar`, and that this captured variable is absent from the local scheme's quantifiers. This witnesses a shared diamond, capture avoidance, and one variable crossing from negative outer Function argument position to positive result position. | Probe command: `cargo test -p infer scratch_oracle_local_diamond_keeps_outer_parameter_shared -- --nocapture` in a detached worktree at `a58eefc3`; assertions inspected formatted schemes, binder counts, and exact TypeVar identities. Temporary probe source was removed. |
| Nested local forward references | A temporary source probe attempted to place two mutually recursive local definitions under an outer parameter so both SCC members could capture one enclosing variable. The Oracle reports `UnresolvedName` for the forward reference from the first local definition to the second. The source form therefore cannot express this desired SCC/capture combination through ordinary sequential local `my` declarations. This is a syntax/lowering limitation observed for this exact form, not evidence that such graph topology is semantically unsupported. | Probe: `scratch_oracle_same_scc_shared_diamond_with_capture` in a detached `main` worktree at `a58eefc3`; the one-off test failed at its no-diagnostics assertion with unresolved `g`. Scratch source was removed; no Oracle files were changed. |
| Pure Function guarded mutual cycle | The source `pub f x = \\y -> g x; pub g x = \\y -> f x` succeeds without diagnostics. Both schemes format as `any -> any -> never`, with zero ordinary quantifiers and zero recursive bounds. A Function-shaped recursive cycle alone therefore does not imply a productive recursive type bound in this witness; this complements, but does not generalize beyond, the nominal-guarded Function SCC result above. | Probe: `scratch_oracle_pure_function_guarded_mutual_cycle` in a detached `main` worktree at `a58eefc3`; inspected both formatted schemes and binder counts. Scratch source was removed. |
| Self-recursive Function result projection | The source `pub returned x = \\y -> returned x` succeeds and formats as `any -> any -> never`, with zero ordinary quantifiers and zero recursive bounds. The earlier Python model's matching graph output is withdrawn and is not evidence. | Oracle probe `scratch_oracle_projection_polarity_matrix` in a detached `main` worktree at `a58eefc3`; its temporary assertion inspected this source alongside the constant and identity witnesses. |

## Open rows

This is not yet a complete observable contract. Still to inspect and record:

- a shared diamond whose paths originate from distinct members of one
  definition SCC and whose common descendant belongs to an enclosing scope;
  ordinary nested local declarations appear unable to express this exact case,
  so characterize it at the graph/constraint level or find another accepted
  source construction before claiming it closed;
- pure Function-only guarded cycles, and additional recursive SCC shapes beyond
  the nominal-guarded mutual witness;
- exact use independence under interleaved constraints and later generalization
  continuations;
- whether a behavior is fixed by tests/observable output or only inferred from
  the machine's implementation order.

The identity-use, unproductive cycle, nominal-guarded mutual Function, and
local captured-diamond probes establish only those exact programs. Recursive
Function SCCs are part of the Oracle target when guarded by the nominal
constructor. A pure Function-only cycle's behavior and a diamond shared across
distinct members of the same SCC remain open; do not infer them from the mixed
witnesses or from the different F5 implementation.

## Research consequence

The sketch's “ordinary extrusion allocates fresh low-level representatives”
claim does not describe the audited Yulang2 `main` implementation. Treat
intrusion as a new candidate semantics and compare observable results, rather
than presenting parent allocation as a direct refactoring of the inspected
Yulang2 extrusion procedure. The new design remains free to choose a shared
SCC graph if its soundness/principality argument and Oracle behavior hold.

## Candidate invariants derived from the lifecycle

These are semantic obligations for a candidate, not a completed equivalence
proof:

1. An SCC is the recursive **monomorphism** region while it is open: references
   between its members constrain their live roots. They must not receive
   independent use-site substitutions before the SCC closes.
2. The SCC is not automatically one polymorphic binder scope. The Oracle asks
   for one generalized result per member root. An implementation may retain one
   shared graph internally, but every member's externally visible scheme and
   binder ownership must be defined as a projection.
3. A dependency edge from an open component to another open component delays
   the source component. Once the target closes, each recorded incoming
   occurrence is instantiated against the target scheme; independent uses
   must not share local substitutions. Any outer variables intentionally
   shared through the session boundary remain shared.
4. All member schemes are available before incoming uses are instantiated, so
   a use cannot observe a partially generalized recursive component.

The first and third obligations are supported by scheduler and use-routing
source/tests. The identity probe observes two distinct incoming types, while
the mutual probes cover one unproductive pure Function cycle and one
nominal-guarded productive Function cycle. These are still individual
observations, not a proof that a parent-based graph has the same principal
solutions.

## Retired finite Python model

An earlier assistant-authored finite Python model was removed after the user
corrected the work direction. Its nineteen checks did not run through either
the Rust solver or the frozen Oracle, and their claimed projection/overlay
results are withdrawn as evidence. The model did not establish its stated
claims against implementation behavior. Preserve this paragraph only as a
history of the discarded detour; Gate B/C evidence must come from mathematical
proof or the actual Rust and Oracle paths.

## Root-projection renaming lemma

The abstract-semantics draft now states a narrow equivariance lemma: on an
already scope-filtered, frozen graph with ordered edge occurrences and their
source evidence retained, injective fresh-parent renaming commutes with
`compact_root_for_scheme` collection followed by root-local polarity census
and one-sided elimination, up to alpha-equivalence. The assumptions preserve
the Oracle candidate predicate `level >= boundary && !non_generic`, edge
weights/evidence/order, and outer identities. This does not prove that the
Oracle's scope query selects the correct edges, and it excludes coalescing,
pinned-interval collapse, sandwiching, role processing, overlays, and
principality.

A scoped read-only `compiler_referee` review found no counterexample under
those assumptions and required two corrections: distinguish the collector
cache key `(TypeVar, polarity, weight)` from recursion key `(TypeVar, polarity)`;
and make the selected ordered edge graph an explicit input because the Oracle
may exclude a lower-bound record through projection evidence. The reviewer
also required keeping `Project` narrowly defined, since the argument does not
cover the other simplification passes. A separate `spec_auditor` confirmed the
narrowed lemma stays within the Reviewed charter and caught a stale ledger
sentence that assigned the cache triple to recursive visits; the table above
now distinguishes the cache triple from the recursion pair. This closes only a
renaming-equivariance lemma, not Gate B/C or implementation authority.

## Scheme lower-record selection

Source audit at frozen Oracle `a58eefc3` confirms scheme collection asks the
scoped query for each lower-bound record. `Unclaimed` records remain direct
inputs. A `project_lower` result of `Excluded` removes that lower record from
the scheme root. `Included` retains the bound with qualifying support and
projection-evidence metadata. Missing/inconsistent proof data or resource
failure returns a projection error instead of silently keeping the edge.

This means an Oracle-compatible intrusion graph needs more than endpoint,
direction, and weight. Edge selection depends on proof records and evaluation
state; some carriers contain a `TypeVar` replay pivot as well as bound-record,
constraint, claim, or derivation IDs. A parent transport must preserve/rewrite
the type-bearing evidence and keep its proof references valid, select and
validate the edges on the original graph at freeze and reuse the ordered
selection after renaming, or show that replacement-owned evidence yields the
same decisions. The preselection route is viable because structural collection
consumes the selected bounds after the query; it still needs a proof that the
selection is frozen at the right boundary and remains valid while member views
are built. `compact_type_var_for_scheme` creates a fresh projection round and
scoped query for each requested root, so sharing preselection across member
roots must preserve the separate per-root decisions and failures; otherwise
the selected-edge masks remain root-local. This gap is outside the reviewed
renaming lemma, which starts after scope selection. The first supported
envelope has not been narrowed to unclaimed bounds; such a restriction would
need explicit compatibility scope and Oracle fixture coverage.

Locators: `constraints/structural_kernel/access.rs::scheme_projectable_lowers_in_scope`,
`compact/collect/mod.rs::compact_var_bounds`,
`compact/surface.rs::compact_type_var_for_scheme`,
`constraints/proof/mod.rs::project_lower_inner`,
`constraints/mod.rs::ProjectionProofCarrier,BinaryReplayDerivation`, and
`constraints/proof/mod.rs::ProjectionEvidence,ProjectionDecision`.

A scoped read-only compiler review confirmed these branches and the replay
carrier's `TypeVar` pivot. It corrected the transport alternatives: the
replacement may preselect and validate on the original graph, then reuse the
selected ordered edges, because structural collection later consumes only
the bounds. Follow-up review confirmed `compact_type_var_for_scheme` creates a
fresh round/query per root and that the draft leaves shared-mask equivalence
as an explicit proof obligation rather than claiming observed divergence. The
draft now makes the required freeze-boundary and view-lifetime proof explicit
for that option.

The abstract draft now states the conservative root-view preparation protocol
in Rust-oriented terms: each compact attempt gets its own projection round,
scoped query, and collector; root generalization may repeat at later constraint
epochs. Reachable lower records are selected lazily, with evidence records
visited before ordinary records and stable order retained within each lane.
The projection round latches errors, while the query gateway can escalate
failures to inference-attempt scope; the compact surface's default fallback is
not evidence of semantic acceptance. A shared component-wide edge mask remains
an optimization obligation, not an assumed equivalence. Oracle root
generalization is sequential and can add constraints/restart, so a single
snapshot for all member views is a replacement design candidate that needs an
equivalence proof. Likewise, all-member failure atomicity is a replacement
safety requirement, not an Oracle publication fact. Public solve results
cannot reveal query-round identities or edge masks; exact protocol
characterization needs source proof or an instrumented Rust trace harness.

The next semantic object is now a sequential root transition, not one
component-wide frozen snapshot. Oracle `quantify_component` generalizes roots
in vector order and may add constraints/restart while preparing each root;
only after all root results are collected does it install member schemes, then
it finalizes them. The candidate draft therefore proposes versioned shared SCC
state: a root step reads the current state, saves the member result at the
point Oracle returns it, then carries forward later bounded post-loop graph
mutations and per-member prerequisite state. The saved result need not
correspond to the resulting solver epoch. Incoming uses select that member
result only after the all-member visibility barrier and receive disjoint
overlays. Projection failure must terminate replacement preparation without a
partial published component; Oracle's compact-surface default is not a valid
result-equivalence claim. This remains a research candidate. The proof must
show observable equivalence to the Oracle's ordered root generalizers,
including cross-root constraint effects; if earlier results cannot remain
valid when later roots update shared state, the versioned-component premise
fails. The Rust-native characterization seam is the in-crate `yu-solver` test
module: real source/HIR collection plus private session solve access can observe
member scheme views and routed use facts; the public `SolvedModule` root-value
projection erases most Function detail.

A further Oracle source audit shows that generalization boundary is per member,
not per SCC: `generalize_boundary(def)` delegates to that def's
`BindingFetch`, and `FetchValue` and `FetchComputation` select different levels.
`quantify_component` invokes the root generalizer separately for each member;
quantified variables are selected from that member's projected root/roles and
pruned within its own result. The Oracle fixture in `analysis/tests/case_03.rs`
uses the same identity-Function graph shape in separate sessions and observes a
quantifier for FetchValue but a unit-boundary variable for FetchComputation.
This is not a source-level mixed-fetch SCC witness; computed-fetch edges inside
a cycle can diagnose. If such a mixed-fetch topology is admitted by the
supported SCC envelope, it is a graph-level counterexample to a single
component-wide quantification decision. Member-indexed `Gen_d`/`P_d` port
selection remains a candidate; each use must freshen member-local generalized
and recursive identities while preserving surviving non-quantified
unit-boundary identity and eliminating one-sided variables. A source nominal
SCC with zero ordinary quantifiers and one recursive bound is observed, while a
separate manual Q/R/B scheme fixture proves both Q and recursive R identities
freshen per use and B remains shared; their combination has not been directly
probed. The draft now uses one `Phi_d` map keyed by source identity, with `P_d`
and `C_d` as role views, and states that imports reject a boundary identity
collision with a per-use identity. Independent compiler-referee and spec-auditor
delta reviews found no remaining blocking or major issue in this port and
recursive-freshness delta. This supports the recorded evidence boundary, not the
port-selection, closure, or principality theorem. The exact paired mixed-fetch
SCC source behavior and zero-Q/R two-use behavior remain open.

Independent compiler-referee and spec-auditor delta reviews of the sequential
root-transition clauses found and closed three major issues: the theorem had
conflated the saved root result with the later solver epoch, omitted state
needed by later roots, and demanded order independence despite Oracle's ordered
mutation. A follow-up semantic review also caught a failure-branch placement
error; the revised protocol aborts before saving a view and stages component
publication. The spec review verified the first proof fragment remains distinct
from the full replacement objective. These reviews cover this lifecycle delta
only; they do not prove boundary-port selection, principality, or the successor
contract and do not authorize implementation.

## New Rust-native recursive-scheme probe (2026-09-30)

In a detached scratch worktree at frozen Oracle revision `a58eefc3`, a focused
unit probe sent this source through `dump_source`:

```yulang
struct step 'value 'next { value: 'value, next: 'next }
my ints(seed: int) = step { value: seed, next: step { value: 1, next: ints seed } }
my mixed(seed: int) = step { value: seed, next: step { value: "s", next: mixed seed } }
my ints_a = ints 0
my ints_b = ints 1
my mixed_a = mixed 0
```

The source lowered without diagnostics. Both `ints` and `mixed` have finalized
schemes with at least one recursive bound. The same `ints` source scheme was
then instantiated twice through `AnalysisSession::instantiate_use`; the
recursive binder recovered through each instantiated root was distinct, and
distinct from the binder from `mixed`. The focused command
`cargo test -p infer --lib source_recursive_function_interval_schemes_and_use_freshening_probe -- --nocapture`
passed in `/tmp/yulang-intrusion-recursive-comparison-probe`.

This closes a source-construction and use-freshening fixture gap for
nominal-guarded recursive Function schemes. It does not show that the two
recursive intervals are mutually subtype-compatible or incompatible. A first
attempt to compare the recovered source binders alone produced no diagnostics
and no pending nominal-cast request; that observation is not a subtype result,
because the source-generated binders expose only part of their interval through
that projection. Keep it out of carrier adequacy claims. A separate hand-built
interval probe with explicit matching lower and upper recursive bounds does
route distinct nominal guards to pending OCast requests in both directions,
but that remains a test-only internal construction, not source-level behavior.

Next, characterize the exact lower and upper recursive-bound payloads of the
source schemes and find a source-level operation whose observable result
depends on their comparison. Only then can the carrier relation be tested
against these recursive intervals. This work used Rust tests against the
Oracle implementation; no auxiliary Python model was used.

## Recursive application outcome characterization (2026-09-30)

The same Rust-native fixture was extended with a source-level consumer whose
parameter is `step int (step int T)`, then calls it with `ints 0` or `mixed 0`
for `T = int`, `bool`, and a distinct nominal `label`. In this extended run,
`mixed` uses `true` as its nested value so the scheme's changed endpoint is
the builtin `bool`. The Oracle check report
has no diagnostics for all six recursive calls. Each case does route one or
more nominal mismatch events, but every captured eligibility result is
`Incomplete { reason: UnknownOrigin(OriginId(1)) }`; none is eligible for a
source-boundary cast diagnostic. This must be read as the Oracle's observed
diagnostic behavior, not as proof that the schemes satisfy a structural
subtyping relation.

Controls: a direct `int` argument to a `bool` parameter produces a check
diagnostic, and an acyclic value explicitly annotated
`step int (step bool int)` produces diagnostics when passed to the same
`step int (step int label)` consumer. This localizes the surprising outcome to
the recursive scheme route rather than establishing general acceptance of
incompatible nominal types.

Raw finalized schemes show the source-level difference. Both have three
quantifiers and one recursive bound. In `ints`, the inner value parameter has
lower payload `q_value ∪ int` and upper payload `q_value`; in `mixed` it is
`q_value ∪ bool` / `q_value`. The recursive root bound's lower side is a union
of its recursive variable and a guarded `step` node, with upper side `Top`.
Thus the observed pending mismatch travels through quantified payloads below a
recursive bound, and its explanation reaches an unknown origin before the
diagnostic gate can decide it.

An additional query at the same OCast producer using `why_constraint` (which
retains scheme-instantiation proof edges) is complete and contains both source
leaves and an `UnknownInternal` origin node. Thus the evidence is mixed: source
provenance exists in the full explanation, while the OCast eligibility query
still rejects the producer because an unknown-origin branch remains. This is
not explained by query truncation.

The origin-bearing edges now isolate the source: at least one `UnknownInternal`
root belongs to a variable-to-variable subtype constraint. That is exactly the
shape emitted for an open recursive/component-local use by
`AnalysisSession::constrain_open_use` (`analysis/session/instantiate.rs`):
`Pos::Var(target_root) <: Neg::Var(use_value)` with
`OriginId::unknown_internal()`. The recursive call inside the `ints` / `mixed`
SCC therefore contributes an intentionally non-source origin to the generalized
proof path. This is not a missing registration for the outer call boundary.
The current eligibility classifier conservatively declines to attach a
diagnostic whenever that recursive internal edge appears alongside the
application's source leaves.

Focused command: `cargo test -p infer --lib source_recursive_ -- --nocapture`
passed 2 source-level tests in the detached Oracle worktree
`/tmp/yulang-intrusion-recursive-comparison-probe`; the manually constructed
explicit-two-sided interval comparison matrix also passed its five focused
tests separately.
This gives an executable fixture for the diagnostic/provenance route. The
remaining semantic question is whether another source context can make this
recursive mismatch eligible or otherwise affect a public inferred result, and
whether the replacement should reproduce this conservative diagnostic gate;
do not model the incomplete event as an accepted subtype edge.

## Recursive endpoint payload through a source-level field selector (2026-09-30)

The source fixture now observes the distinct recursive endpoint payloads through
a polymorphic selector over the nominal struct's generated field methods:

```yulang
struct step 'value 'next { value: 'value, next: 'next }
my ints(seed: int) = step { value: seed, next: step { value: 1, next: ints seed } }
my mixed(seed: int) = step { value: seed, next: step { value: true, next: mixed seed } }
my get_inner_value(x: step int (step 'a int)) = x.next.value
my ints_inner_value = get_inner_value (ints 0)
my mixed_inner_value = get_inner_value (mixed 0)
```

The Oracle reports `get_inner_value : step(int, step 'a int) -> 'a`, then
infers `ints_inner_value : int` and `mixed_inner_value : bool`, with no lowering
or check diagnostics. The dedicated assertion probe passed, and the consolidated
command `cargo test -p infer --lib source_recursive_ -- --nocapture` passed all
four matching source probes in detached worktree
`/tmp/yulang-intrusion-recursive-comparison-probe` at frozen Oracle revision
`a58eefc31e22141574b6f20c6a5748151c6d79f1`.

This is stronger source-level evidence than the diagnostic-only application
probe: the recursive schemes preserve endpoint payload differences through
instantiation and nominal field selection into public inferred result types.
It does not prove that those schemes are principal, characterize the complete
subtype carrier, or establish the SCC-intrusion replacement relation. In
particular, keep the conservative OCast diagnostic result and this inferred-type
observation as separate public observations.

A follow-up raw-scheme print showed both outer schemes format identically as
`int -> step int 'a`, while the raw quantified inner intervals are
`q ∪ int ≤ q` and `q ∪ bool ≤ q`; the distinct productive recursive root
interval is a separate binder. The exact extracted nodes and the conditional
join calculation are recorded in
`notes/progress/2026-09-30-intrusion-recursive-selector-adequacy.md`. This
confirms that formatted scheme text alone is too weak to characterize this
Oracle behavior.

Next close the fixture-level adequacy calculation for these intervals: relate
the selected roots at their actual epochs to the source view, define their
fresh instance relation with shared anchors, and show how the nominal selector
projects the least endpoint payload to the public `int` / `bool` results. Then
continue toward envelope-wide root simulation and principality. The F5 shape
remains withdrawn as the target.

The two selected root traces and the external per-use fresh maps are now
captured for this fixture in
`notes/progress/2026-09-30-intrusion-recursive-root-epoch-capture.md`. They
confirm the local inputs for the next calculation, but do not themselves prove
selector projection or an intrusion-to-Oracle simulation. The selector calls
also emit two `UnknownOrigin`-incomplete OCast classifications with complete
explanations and no diagnostics; this is a separate outcome from the inferred
`int` / `bool` results, not a successful-subtyping observation. A Rust trace
shows each `step <: int` event is a productive union branch reached through
the second invariant argument of the selector's `step <: step` comparison.
The classifier-specific explanation now traces both events through recursive
bound replay to `UnknownInternal(OriginId(1))`. This establishes a reachable
classification blocker for this fixture, not subtype acceptance or the origin's
source. Details and review scope are in the root-epoch capture note.
