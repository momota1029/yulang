# R70 owner map: `candidate_extrude` entry, mutation, and replay handoff

Date: 2026-10-19
Sprint: `ordinary-extrusion-invariant-20261019-r70`, revision 1
Contract SHA-256: `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`
Code baseline: `c84f3f98673af3993dea85c5d9ecb938463738a3`
Author: `/root` (Luna/high coordinator; requested model/effort recorded, observed UNKNOWN)
Outcome class: source/native owner map; not a proof, counterexample, semantic decision, code change, or parent closure.

## 1. Exact entry route and scope

The production calls are in `crates/yu-solver/src/lib.rs::dispatch_live_item` at the two structural Value branches around lines 12572 and 12585. With `shadow-apply-candidate` and `candidate_graph.is_some()`, the lower non-row is extruded positively to the upper row's value level, or the upper non-row negatively to the lower row's level. On a changed result, the caller records the typed pair and diagnostic edge, derives the contextual rewrite relation, retains the rewrite, then enqueues the rewritten Value item. A direct call in a test helper is outside this packet's theorem scope.

The ordinary production path is inside `constrain_live_item_with_inferred_entry` / `run_candidate_typed_drain`: the outer typed drain owns `typed_worklist`, the active comparison and its processing/context records. It dispatches the current item, lets `candidate_extrude` return, then the dispatch branch enqueues the rewritten comparison. The drain later consumes work items and handles `replay_ack`; queue consumption and acknowledgement are later owners in `lib.rs` around lines 12139–12172 and 12323 onward. The drain's full termination is outside R70's fixed outcome.

From these callsites one can derive the feature route, a present candidate graph, the source comparison endpoints, which endpoint is a non-row, which receiving row supplies the target level, and the positive/negative root polarity. The static owners do **not** validate every ordinal, Function term handle, effect view/member, capture incidence, bound-origin fiber, or scoped record before the call. Those remain explicit well-formedness assumptions unless the proof derives them from pinned constructors. `scoped_enabled` and processing-state branches are read inside the owners; neither may be silently fixed to one mode. The R70 theorem is conditional on successful fallible capacity/identity operations and valid reachable owner records; failure rollback is not proved here.

## 2. Operation-local owners and write order

`candidate_extrusion.rs::candidate_extrude` begins one operation occurrence and records the starting parent index. Its local state is:

- `rows: HashMap<Key, ExtrusionEndpoint>` keyed by endpoint kind/identity, polarity and target level;
- `structure` with the same key shape for remapped Function/effect-view terms;
- `work` for structural reconstruction and `pending_bounds` for bound visits/transports;
- `view_remap` keyed by `(old view, mapped tail)`;
- `initialized_allowances` for the final replay phase; and
- `charge`, updated as temporary vector/map capacities grow.

The loop prefers `work.pop()` and uses `pending_bounds.pop()` only when structural work is empty. `Work::Visit` canonicalizes first. A row at or below target maps to itself and does not traverse its bounds. A deeper row snapshots the lengths of its polarity-selected direct-row and exact-endpoint lists **at that Visit**, allocates a fresh Value/Effect row at the fixed target, retains its actual parent, inserts the row memo before scheduling children, and installs the opposite-side source link. Positive selects lower bounds; negative selects upper bounds. Selected children are keyed by the same target and polarity. Their mapped bounds are installed later by `Work::Bound`, with exact evidence/origin transport.

This is a mutating traversal. A later Visit can observe an earlier Visit's synthetic opposite-polarity source link. The complementary lane found a concrete required case: one positive Function has the same high Value row `v` in its argument and result, with empty entry bounds. Argument variance is negative and visited first. The negative Visit creates `n` at target `L` and appends `n` to `v.lower`; the later positive Visit snapshots that newly grown lower side, creates `p`, appends `p` to `v.upper`, and schedules `n` into `p.lower`. A model frozen to the entry bounds loses this actual cross-polarity edge. The proof lane has been told to use per-Visit prefixes and include these links. This trace is a transition requirement, not a counterexample to the current operation.

Function structural ownership is in the `Work::Function` arm. It keeps the ordered children `(argument value, argument effect, result effect, result value)` and flips polarity on both argument ports while preserving polarity on both result ports. A changed child is converted back to a `Term` at that child's expected polarity; reconstruction uses the original Function polarity. A valid sharing invariant must show that repeated row keys share one row image and repeated structural keys share one structure image. `term.rs` and `lib.rs` own term conversion/interning; this map does not assert a whole-session allocation bound.

For `Allowance`, `Support`, and `AnnotationMember`, `Work::Visit` reads the actual view tail. If present, it visits the tail row and schedules `Work::EffectView`; reconstruction uses the operation-local `(old view, mapped tail)` map. The `Work::IncomingAllowance` arm visits each recorded positive-effect capture source, maps the view, installs the negative Allowance bound, and transports the original fibers/origins. The exact view-copy and effect-bound owners are `candidate_effect.rs`; source qualification reads `candidate_source.rs` and `candidate_value_graph.rs`; contextual scope transformations are in `candidate_scope.rs` and `candidate_context.rs`.

`candidate_intrusion.rs` owns occurrence IDs, retained parent rows, dirty marking, and the output `PairGroup`. `candidate_extrusion.rs` owns physical selected-side insertion and the calls that transfer exact bound fibers and origin metadata. These are separate state writes; parent metadata is not itself a bound edge, and `Work::Bound` does not prove later propagation or source validity.

Temporary map/work storage growth is charged through `candidate_scratch_growth`; `candidate_extrude` drops the local containers and subtracts its recorded scratch charge on its return path. Row arrays, term interning, parent/output indexes, captured views, contextual evidence, replay children, typed-worklist capacity and later drain storage have other owners/accounting paths. No total time or memory bound is claimed by this owner map. A proof must distinguish unique memoized visits from repeated list/fiber products and replay expansion.

## 3. Return boundary and replay ownership

After the work loop, the operation resolves the root from `rows` or `structure`, calls `finish_candidate_extrusion`, and then calls `candidate_replay_bound` for every installed incoming allowance. `candidate_replay_bound` observes the current opposite-bound count and forms a contextual replay for each actual opposite item. `candidate_context_begin_replay` constructs replay relations from the current attached lower/upper fiber lists and retains them under a `ReplayOperation`.

`candidate_context_drive_replay(replay, None)` has no provenance with which to synchronously drive a typed drain. For a fresh nonempty operation on a successful drive, it transfers all retained child items to the outer typed worklist: `queued == children.len()` and `consumed == 0`. A zero-child operation can retire immediately. If a later enqueue fails, a strict transferred prefix can remain and the retained operation owns the remainder. Thus the invariant must distinguish relation children retained in `ReplayOperation`, queue items already transferred, and later `replay_ack` completion. No child is semantically executed by `candidate_extrude`'s replay helper itself.

The enclosing dispatch call then records and enqueues the main rewritten Value comparison. The outer `run_candidate_typed_drain` owns execution/transport and later acknowledgement. `settle_candidate_intrusion` is another outer consumer. Their presence supplies a handoff path only; this owner map proves neither complete drain termination nor universal replay adequacy.

## 4. Cost and proof boundary

Candidate cost terms must be separated at least as:

1. unique row/structure/view discovery and operation-local map/worklist work;
2. selected bound and source-link installation;
3. bound-origin/fiber iteration and contextual evidence construction;
4. term reconstruction/interning;
5. initialized-allowance replay relation products and typed-worklist transfer; and
6. caller-owned later typed drain, propagation, and acknowledgement.

Counts must be derived from the actual input graph and live incidence lists. `candidate_context_begin_replay` can form products over attached fibers; a claim based only on distinct rows or structural edges is insufficient. The staged Simple-sub relation draft is not an algorithm authority and supplies no Yulang replay or total-runtime theorem. No linear bound, global solver termination, source Generalize, evaluator correctness, soundness, principality, or A/B closure follows from this map.

## 5. Pin and completion receipt

The contract's 20 direct SHA-256 dependencies matched the candidate baseline at selection. The direct implementation owners for this map are `candidate_extrusion.rs`, `candidate_intrusion.rs`, `candidate_effect.rs`, `candidate_context.rs`, `candidate_value_graph.rs`, `candidate_scope.rs`, `candidate_source.rs`, `candidate_scheme.rs`, `term.rs`, and `lib.rs`; the authority/reference owners are exactly those in the frozen contract. No test/build/probe was run. No source semantics, code, expected output, fixture, or production admission changed.

## 6. Counter-reading and freeze receipt

The complementary static counter-reading is frozen at `notes/progress/2026-10-19-r70-extrusion-countertrace.md` (SHA-256 `6bb29d09fbf1440c964899815b95e06244cdd9ccc67ddf0dbe76d2016ec15b8e`) with handoff `tasks/agent-loop/inbox/20261019-r70-research.md` (SHA-256 `4fbb70a13a205f4b0cef9990d7ad630c0bc956a611ebcdf4461a2886e1bd90e8`). Its bounded result found no source-qualified counterexample and no theorem certification; it supplies the mixed-polarity mutation and replay-frontier facts summarized above. Its 20 dependency pins matched baseline and inspected live bytes. No tests, builds, probes or executable mutations ran.

This owner map and its handoff are now frozen by `/root`; the exact hashes are recorded in the handoff. This map identifies the active handoffs and predicates still needing proof. It does not adjudicate the constructive proof/countertrace or mark the operation target closed. Luna remains the sole Git owner.
