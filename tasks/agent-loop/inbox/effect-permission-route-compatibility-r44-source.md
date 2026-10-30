# R44 source correspondence: route compatibility

Status: **NO_SAFE_CONSUMER_SLICE**. Frozen source handoff; author STOP after
publication. This is a bounded source characterization, pending independent
review. It establishes no Rust execution, whole-language theorem, consumer
authorization or production promotion.

## Objective, authority and baseline

Determine whether the existing receiving experiment supplies the exact
module FreshRoute/native-incidence premise required by R43 without changing
inference. Preserve annotation permission, actual inflow and Catch subtraction
as distinct facts under `2026-10-10-annotation-effect-hygiene-integration.md`
sections 1–1.2. No semantic alternative is selected here.

Baseline: `b2c4906821b9e0c3b01cb18321b1b7340a8f3c5f`, branch `yulang3`.
Contract: `tasks/agent-loop/sprints/effect-permission-route-compatibility-20261031-r44.md`,
SHA-256 `4342109c2c6ff5fde25a69b38b267bfc41e692189cf3fd330caf35dfe9177df1`.
The following pins were rehashed before this artifact was written; all match.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/UseScopedPermissionR43.lean` | `83ede0609353cec9dfde8258fa86f0f7c72aadef647dbe0819fe326776e46f8d` |
| `tasks/agent-loop/inbox/effect-permission-use-binding-r43-review.md` | `fcad39e4126b1d2d826cc1b32c03e359b43fa5ad7bc5a6864119b266a0e5bc6b` |
| `tasks/agent-loop/inbox/effect-permission-use-binding-r43-rust.md` | `c04110859cafa42cffa0d52982f6c9f52fbdd474512fa1054f37bc72f19aa9ee` |
| `crates/yu-solver/src/candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` |
| `crates/yu-solver/src/candidate_scheme.rs` | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` |
| `crates/yu-solver/src/candidate_effect.rs` | `73ad01324356672f1e45e56ea18d6f5bf0ded8628cce56e884960eb29bd5786d` |
| `crates/yu-solver/src/lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` |
| `notes/theory/lean/YulangClosure/EffectPermissionResidualR38.lean` | `e5657e0b8affaaa0ffef6543c8e329957a1519a04a194392dbd245064a623642` |
| `tasks/agent-loop/inbox/effect-permission-residual-join-r38-rust.md` | `768098b3cbb313ee6b317abf05a922bb85f3af18bf327b4d412a5ba80f168e4f` |

These are working-tree source pins, including the explicitly frozen dirty
snapshots. They are not assertions that those files equal the baseline commit.

## Source derivation

1. `candidate_receiver.rs:326–332` constructs a new candidate session and
   immediately calls `execute_receiving_assembly`. `lib.rs:10436–10441`
   implements `try_new_candidate` as `try_new`, then `start_candidate_graph`.
   `candidate_scheme.rs:2456–2469` creates `GraphState::default()` and initializes
   definition graph slots to `None`; the default route vector is empty.

2. `candidate_receiver.rs:350–365` requires exactly one definition use and
   checks that its parent definition root is `schema.answer` and its target
   definition root is `schema.relay`. These roles identify the receiving source
   owner and relay provider root. The operation provider is a different identity:
   `schema.provider` is the original operation expression's `HirOccurrenceId`.

3. `candidate_receiver.rs:367–393` executes the relay and answer source action
   schedules. The `Action::Module` branch constructs the full use identity as
   `DefinitionUseId::new(batch.collection_artifact.clone(), occurrence.clone())`
   and calls `route_internal`. The bounded assembly does not call
   `execute_candidate_graph_plan` (`candidate_scheme.rs:3074`), whose export
   capture at `:3149` and publication at `:3209` populate definition graph slots.
   Executing the original source schedule is not that export-capture step.

4. `lib.rs:18228–18251` validates the plan-owned use, then obtains the original
   target-root and use-value component terms. Its value key uses the corresponding
   original live row ordinals. It calls `route(..., RoutedUseKind::Internal)`.
   `validated_route_use` at `lib.rs:19487` checks the stored cause's full use ID.

5. `route` (`lib.rs:19361–19435`) admits the original-term constraint, propagates
   its value relation and records `RoutedUseProvenance { use_id, fact, kind }`.
   It appends no FreshRoute and constructs no retained FreshUse term/row map or
   context-use identity. Therefore the initially empty module FreshRoute vector
   receives no same-use route from this bounded receiver routing path. The
   conclusion uses initialization and the actual constructor path, rather than
   deriving global absence merely from the label `Internal`.

6. The alternative Incoming constructor has an unmet earlier prerequisite.
   `route_candidate_graph` (`candidate_scheme.rs:4369–4394`) first requires
   `state.graphs[target].as_ref()`, extracting the captured live root, boundary,
   source frontier and obligations. The receiver has not performed the export
   capture/publication establishing this graph. Only after that prerequisite
   does it recapture and call `instantiate_candidate_graph`.

7. `instantiate_candidate_graph` (`candidate_scheme.rs:4923–4989`) calls retained
   FreshUse, obtaining a fresh lower term and one shared row/term map. It derives
   `receiving_owner` from the actual `DefinitionUse.parent`, retains the fresh
   context, calls `route(..., IncomingStructured)`, and then publishes
   `FreshRoute { use_id, source_owner: receiving_owner, provider: target_root,
   graph, rows, retained }`. This is the constructor R43 requires. The Internal
   constructor supplies neither its capture premise nor its retained result.

8. The receiver's residual remains the original collected fact. It withholds
   the unique slot-51 fact at `schema.edge_scrutinee` (`candidate_receiver.rs:375`)
   and reads its original lower/upper terms at `:396–399`. Actual arrivals are
   enumerated by lower-bound traversal at `:400–453`. No FreshRoute graph-row
   image is selected for this residual. Even a separately available FreshRoute
   would require a proved relation to the residual instance being consumed.

## R43 interface and the remaining arrival boundary

`FreshRoute` ownership fields are declared at `candidate_scheme.rs:425`.
An exact route lookup must use the full `DefinitionUseId` and validate
`source_owner == Definition(schema.answer)` and `provider == schema.relay`.
The route's retained context is available through
`RetainedFreshUseMaps::observed_context_use` (`candidate_scheme.rs:606`).
`bind_native_formal_entry_permission_use` (`candidate_scheme.rs:505`) binds an
actual retained permission through that exact route's native Function incidence.
Its result includes the original permission coordinates, concrete members,
mapped row, definition-use identity and context-use identity. This function
does not create a missing route or certify an arrival/Catch relation.

The actual operation terminal retains distinct source evidence:
`AnnotationMember(view, member)` selects a view whose `ViewOrigin::Operation`
contains the original operation occurrence and declaration (`candidate_effect.rs:341–368`).
The receiver already compares those coordinates, the family, closedness and
selection (`candidate_receiver.rs:461–474`). `candidate_copy_effect_view`
(`candidate_effect.rs:1444`) preserves operation origin when copying. This
origin alone does not associate a provider with the R43 receiving instance.
Permission membership, actual arrival, selected handler and residual instance
must all hold before any future consumer can suppress an operand.

## Discriminating witnesses and rejected shortcuts

- Minimal constructor witness: start from the new session, route the one
  validated receiver use through `route_internal`, and inspect the owner paths.
  There is an Internal receipt for the full use ID and no FreshRoute append.
  Replacing the absent FreshRoute with that receipt assumes the exact missing
  constructor result. This witness is a source derivation, not a runtime trace.
- A second admission of the same full use ID cannot repair this result:
  `route` asserts `!routed_use_positions.contains(id)` before admission at
  `lib.rs:19373`, then inserts that ID at `:19411`. Calling Incoming after
  successful Internal admission violates the one-admission invariant.
- Equal IDs or equal lower terms do not make the two constructor results
  equivalent. Neither equality supplies a captured graph, retained native
  incidence, FreshUse map or context-use identity.
- A FreshRoute belonging to another use is invalid even when it instantiates
  the same relay root or has equal mapped rows. A same-family arriving terminal
  from another operation occurrence must also forward; family membership cannot
  replace the provider-occurrence check.

No randomized search, seeds, ranges, mutations or oracle comparison were run.
The method is inspection of the owning constructors. The Rust source is the
implementation evidence; the separate proof lane must keep its modeled
transition assumptions explicit. Hash equality authenticates the inspected
bytes and does not independently prove their semantics.

## Outcome, limits and handoff

**NO_SAFE_CONSUMER_SLICE**: R43's exact-use FreshRoute premise is not supplied
by the current bounded receiver. The first absent Incoming prerequisite is
the stored captured definition graph; the Internal route also constructs no
FreshUse maps/native incidence/context. Replacing routing, admitting twice,
borrowing another route or manufacturing a route is outside this contract.

Recommended next action: primary selection of a separate exact implementation
contract for either authentic Internal-route permission incidence or a deliberate
Incoming/FreshUse experiment with its capture and residual-instance obligations.
This note selects neither design and authorizes neither implementation.

Verification: `git rev-parse HEAD`, `sha256sum` for every contract pin, and
targeted `rg`/`sed` source reads. No builds, tests, Cargo, Lake, formatter,
scratch/cache/target, environment/worktree, source edit, Git mutation or child
worker. Rust compilation/runtime remain unobserved. Actual model: UNKNOWN;
exact elapsed runtime and peak CPU/RAM: UNKNOWN. The 700-second lane budget was
not used as authority for additional work.

Commit packet: exact changed/leased path is this file only; baseline and
dependency hashes are above; no dependency changes observed; independent review
PENDING; source reads and hashes only. Proposed commit message:
`research: record R44 Internal versus FreshUse route obstruction`.
Shared-record delta left to the primary: record this bounded obstruction while
keeping provider-arrival/Catch consumption, original A/B and whole-language
soundness OPEN. Author writes stop before independent review.
