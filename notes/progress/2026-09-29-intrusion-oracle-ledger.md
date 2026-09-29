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
| Root-local polarity projection path | Oracle scheme projection starts each member root at positive polarity, expands a variable through lower bounds at positive polarity and upper bounds at negative polarity, caches by `(TypeVar, polarity, weight)`, and detects recursive re-entry by `(TypeVar, polarity)`. After building the compact regular root, simplification collects polarities across the root and recursive-bound table and erases eligible one-sided variables; bipolar occurrences keep the same variable identity. The exact erasure candidate predicate is `level >= boundary && !non_generic`. For a parent-renaming proof, preserve that predicate and weight annotations; numeric level values need not be identical when a child-level variable is raised to the boundary. This is source behavior, not a required representation for the replacement engine. | `crates/infer/src/compact/collect/mod.rs::compact_root_for_scheme,compact_var_side,compact_var_bounds`; `crates/infer/src/compact/analysis/occurrence/mod.rs::collect_var_polarities`; `crates/infer/src/compact/analysis/mod.rs::eliminate_polar_variables_with_roles_and_non_generic,is_simplification_candidate`. |
| Source-level mutual recursive definitions | A temporary public-surface probe for `pub f x = g x; pub g x = f x; pub number = f 1; pub function_value = g (\\z -> z)` completed with no lowering diagnostics. Both member schemes formatted as `any -> never`; both incoming use schemes formatted as `never`. This is an observed result for this unproductive call cycle, not evidence about every guarded/productive SCC shape. | Probe command: `cargo test -p infer scratch_oracle_mutual_scc_independent_incoming_uses -- --nocapture` in a detached worktree at `a58eefc3`; probe code was temporary and is not part of the Oracle commit. The existing committed scheduler fixture `crates/infer/src/lowering/tests/case_06.rs::body_lowering_keeps_forward_cycle_in_one_scc` independently asserts that `my a = b; my b = a` merges and quantifies one component. |
| Nested self-recursive lambda source | The accepted source `pub f = \\x -> \\y -> f` formats as `any -> never` in the Oracle. This pure Function-only shape does not retain a recursive scheme bound; it differs from the nominal-guarded mutual Function SCC recorded below. | Probe command: `cargo test -p infer scratch_oracle_guarded_recursive_function_scheme -- --nocapture` in a detached worktree at `a58eefc3`; temporary probe code removed with that worktree. |
| Source-level recursive nominal and Function roots | A source-level self-recursive nominal value `struct loop 'a { next: 'a }; pub helper = loop { next: helper }` is accepted with scheme `loop 'a`, zero ordinary quantifiers, and one `recursive_bounds` entry. A recursive Function binding `pub helper x = loop { next: helper x }` is accepted with scheme `any -> loop 'a`, one ordinary quantifier, and no `recursive_bounds`. Thus the Oracle demonstrably supports guarded recursive type bounds in general, while this Function-valued witness does not create an R binder. | Probe command: `cargo test -p infer scratch_oracle_recursive_function_bounds_from_source -- --nocapture` in a detached worktree at `a58eefc3`. Probe inspected formatted scheme, `quantifiers.len()`, and `recursive_bounds.len()` for each source. Temporary probe code was removed. |
| Guarded mutual Function SCC with recursive bounds | The source `struct loop 'a { next: 'a }; pub helper x = loop { next: \\y -> g x }; pub g x = loop { next: \\y -> helper x }` succeeds without diagnostics. Both member schemes format as `any -> loop 'a`, each with 2 ordinary quantifiers and 1 recursive bound. Each recursive lower interval is a union of a variable and a Function whose result is `loop` with a recursive argument bound; the two bounds' upper sides point to the opposite member's recursive variable. This is an actual source-level SCC witness combining Function structure, nominal guarding, cross-member recursion, and R bounds. | Probe command: `cargo test -p infer scratch_oracle_recursive_function_shape_matrix -- --nocapture` in a detached worktree at `a58eefc3`; the probe inspected both members' scheme binder counts and recursive-bound graph nodes. Probe source was temporary and removed after the run. |
| Local diamond and captured rigid endpoint | The source `my outer x = my inner y = ({left: x, right: x}, y); inner` succeeds without diagnostics. The local scheme is `'a -> ({left: 'b, right: 'b}, 'a)` with one quantifier; the outer scheme is `'a -> 'b -> ({left: 'a, right: 'a}, 'b)` with two. Raw arena checks confirm both local record paths and the outer input use the same `TypeVar`, and that this captured variable is absent from the local scheme's quantifiers. This witnesses a shared diamond, capture avoidance, and one variable crossing from negative outer Function argument position to positive result position. | Probe command: `cargo test -p infer scratch_oracle_local_diamond_keeps_outer_parameter_shared -- --nocapture` in a detached worktree at `a58eefc3`; assertions inspected formatted schemes, binder counts, and exact TypeVar identities. Temporary probe source was removed. |
| Nested local forward references | A temporary source probe attempted to place two mutually recursive local definitions under an outer parameter so both SCC members could capture one enclosing variable. The Oracle reports `UnresolvedName` for the forward reference from the first local definition to the second. The source form therefore cannot express this desired SCC/capture combination through ordinary sequential local `my` declarations. This is a syntax/lowering limitation observed for this exact form, not evidence that such graph topology is semantically unsupported. | Probe: `scratch_oracle_same_scc_shared_diamond_with_capture` in a detached `main` worktree at `a58eefc3`; the one-off test failed at its no-diagnostics assertion with unresolved `g`. Scratch source was removed; no Oracle files were changed. |
| Pure Function guarded mutual cycle | The source `pub f x = \\y -> g x; pub g x = \\y -> f x` succeeds without diagnostics. Both schemes format as `any -> any -> never`, with zero ordinary quantifiers and zero recursive bounds. A Function-shaped recursive cycle alone therefore does not imply a productive recursive type bound in this witness; this complements, but does not generalize beyond, the nominal-guarded Function SCC result above. | Probe: `scratch_oracle_pure_function_guarded_mutual_cycle` in a detached `main` worktree at `a58eefc3`; inspected both formatted schemes and binder counts. Scratch source was removed. |
| Self-recursive Function result projection | The source `pub returned x = \\y -> returned x` succeeds and formats as `any -> any -> never`, with zero ordinary quantifiers and zero recursive bounds. The finite projection model's graph with `root.lower = (x -> inner)` and `inner.lower = (y -> root)` projects to the same nested `Any -> Any -> Bottom` shape after positive-only recursive collapse. | Oracle probe `scratch_oracle_projection_polarity_matrix` in a detached `main` worktree at `a58eefc3`; its temporary assertion inspected this source alongside the constant and identity witnesses. Model check: `root-local projection` in `notes/progress/2026-09-29-intrusion-finite-model.py`. |

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

## Intrusion finite closure model

Added `notes/progress/2026-09-29-intrusion-finite-model.py`, a small executable
implementation of the pure closure rules recorded in the abstract-semantics
draft. `python3 notes/progress/2026-09-29-intrusion-finite-model.py` passes
nineteen checks covering injective parent-renaming commutation, identity sharing,
directed variable flow, Function polarity, invariant constructor arguments,
shared diamond, outer capture, nominal recursion, union/intersection branches,
one-sided root erasure/expansion in both directions, root-local projection of
two roots sharing a variable, nested positive-only recursive Function collapse,
and separate overlays. A non-injective quotient counterexample confirms that
mapping distinct variables to one parent erases a directed flow edge. The
projection checks reproduce `any -> int` for the unused-argument shape, retain
the identity Function's bipolar variable, preserve an outer rigid variable, and
collapse a positive-only recursive Function result to `Bottom`.

This validates the local edge-transport proof sketch against its executable
encoding and characterizes a bounded root-projection fragment. The model does
not encode the Oracle's recursive-binder table, implement principal solutions
or SCC member schemes, or model production inference. It does not close the
central principality obligation.

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
