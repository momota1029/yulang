# Effect-drain Value-witness reachability audit

Status: frozen, unreviewed research-only source characterization and conditional
derivation. No authentic source counterexample, source impossibility theorem,
rejection theorem, or implementation authority is claimed.

Baseline: `74e027c9f8cbf37cb11acf4ce4a53b9613dbfedb`, re-pinned by
`git rev-parse HEAD` before reads. Governing authority: top-level inference
principles §4 and compiler-engineering “Deterministic Simple-sub inference” /
“Diagnostics boundary”. Appropriate error detection and safe publication are
required; exact diagnostic identity and complete restoration are not general
requirements. The parent retains the constructive theorem and independent review.

## Objective and result

Determine whether an authentic source-generated Value incompatibility can be
processed by an Effect-root typed drain and omitted because diagnostic
completion clears the delta before the induced-Value witness loop.

The clearing order is real. The assumed predecessor of saved queued Value work
coexisting with a newly started Effect drain is excluded by actual entry guards.
Pure Effect processing also cannot newly close a Value dependency SCC in this
implementation. The unresolved predecessor is **Value graph mutation before an
Effect child begins**, specifically a zero-product fresh-bound restoration.
This audit neither constructs that predecessor from source nor proves that all
authentic restoration histories exclude it.

## Exact consumer chain

All line references below identify the pinned source, not a second model.

1. `lib.rs:12138` `start_typed_drain` asserts an empty `typed_worklist`, clears
   diagnostic scratch, seeds the initial relation, and enqueues the initial task.
2. `lib.rs:12225` `step_typed_drain`, Transport with no current item, invokes
   `settle_candidate_intrusion(None)` for an Effect root whenever its queue is
   empty. This settles **all** retained intrusion parents, including Value parents.
3. `candidate_intrusion.rs:358` builds the dependency graph and chooses every
   distinct parent/copy pair sharing an SCC. `merge_candidate_rows` appends both
   bound sides, updates representatives/generation, transfers bound provenance,
   and replays each merged owner's lower against its uppers (`:595` onward).
   A Value merge therefore calls `candidate_replay_bound` on a Value owner.
4. `candidate_extrusion.rs:763` `candidate_replay_bound` chooses a Value task for
   Value endpoints. Its `candidate_context_drive_replay(replay, None)` queues
   children into the **current** drain; it does not create a separate Value-root
   diagnostic drain (`candidate_context.rs:3088`). The parent diagnostic root is
   absent because intrusion received `root=None`.
5. `lib.rs:12376` dispatch of an incompatible Value pair records a direct witness
   with `DiagnosticCompletion::Pending`; admission adds the pair to the delta
   (`:12887`, `:12763`). Dispatch itself does not report that witness.
6. Diagnostics (`lib.rs:12295`) first calls
   `candidate_replay_effect_conflicts(initial, ...)`, then
   `complete_diagnostic_delta()` (`:12300`). Completion writes persistent
   `Complete(witness)` entries (`:13422`) and calls
   `clear_diagnostic_scratch()` (`:13457`), which clears both delta and index
   (`:13538`). The subsequent Effect-root loop over `diagnostic_delta` (`:12303`)
   has zero iterations on successful completion.

The Effect conflict replay reports only `IncompatibleEffect`
(`candidate_effect.rs:659`–`:731`); it does not consume a Value memo witness.
The witness is retained in the persistent memo, so the established loss is of
**this drain's reporting opportunity**, not destruction of the witness or proof
that no later Value root can report it. The old synchronous fallback contains
the same clearing order (`lib.rs:12091`–`:12103`), but a live candidate graph
returns through `run_candidate_typed_drain` before that fallback.

## Entry guards and a conditional exclusion

`candidate_begin_bound_restoration` asserts an idle worklist before physical
insertion (`candidate_extrusion.rs:668`). A restoration replay child in Idle
also returns an availability error when the worklist is nonempty, before
`start_typed_drain` (`candidate_context.rs:3013`–`:3034`). Thus a hand-built
preexisting queue containing Value work cannot be used as an authentic
Effect-root predecessor. A retained parent frame or restoration handle is not
a license to bypass these guards.

The intrusion dependency graph has a useful stronger sort property:

- A Value row points to bound Value rows or Function constructors.
- A Function points to its Value argument/result and Effect ports.
- An Effect row points only to Effect bound endpoints; Support/Allowance points
  only to its Effect tail. Other Effect endpoints contribute no graph node.

These are the exhaustive branches of `candidate_intrusion.rs:388`–`:469` and
`Dependencies::intern` (`:614`). Therefore every path starting at an Effect
node stays within Effect nodes. No SCC contains both a Value/Function node and
an Effect node. In particular, the comment about an Effect dependency closing
a mixed SCC cannot itself justify Value reachability in this graph.

**Conditional source-rule derivation.** Quantify over successful, finite
candidate typed drains whose initial task is Effect, with the constructors in
the inspected files and no concurrent mutation. Assume at entry that every
distinct retained **Value** parent/copy pair lies in different SCCs of the
current dependency graph. Then this drain admits no Value work and has no new
Value diagnostic delta. The entry queue is empty except its Effect seed.
Effect dispatch, endpoint checking, filter execution, and bound replay are
sort-preserving (`candidate_extrusion.rs:843`, `candidate_effect.rs:889`,
`candidate_context.rs:2744`). Effect representative changes transport bound
relations but enqueue no Value task (`candidate_context.rs:3125`). Effect
merges cannot change reachability between Value nodes because an Effect path
cannot return to Value. Consequently intrusion never chooses a Value merge;
by induction every queued/current item is Effect. The witness loop's empty
delta is harmless under this premise.

The entry SCC premise is a **candidate assumption**, not an established
all-source invariant. Queue emptiness does not imply it. This derivation also
does not exclude preexisting persistent Value witnesses requiring later replay.

## Missing authentic predecessor

`candidate_begin_bound_restoration` physically inserts its bound, marks
intrusion dirty, and saves the opposite count. When that count is zero,
`candidate_step_bound_restoration_child` retires the restoration without
starting a typed drain (`candidate_extrusion.rs:673`–`:677`, `:715`–`:719`).
No intrusion settlement is performed on that return. This is a real constructor
route, rather than saved Value queue state.

Authentic incoming use follows
`route_candidate_graph` → `capture_candidate_graph` →
`instantiate_candidate_graph` → `freshen_candidate_graph` →
`begin_candidate_fresh_bound` → `candidate_begin_bound_restoration`
(`candidate_scheme.rs:946`, `:965`, `:1221`, `:1277`). Local Name use follows
`Action::Local` → `route_candidate_local_run` → `step_candidate_local_use` →
the same fresh-bound owner (`candidate_source.rs:680`,
`candidate_scheme.rs:1354`, `:1500`). Bounds preserve captured side and occur in
captured graph order; the owner does not batch all Values before all Effects.
An Effect restoration with a replay child can therefore be the next diagnostic
drain after a zero-product Value restoration.

Fresh preparation allocates/remaps rows and reconstructs Function nodes but
does **not** retain extrusion parents (`candidate_scheme.rs:981` onward).
Parents are created by `candidate_extrude` (`candidate_extrusion.rs:121`).
Capture excludes bound expansion for older shared rows (`candidate_scheme.rs:570`)
and freshening preserves shared/non-generic rows (`:1008`). These facts reduce
the search, but do not by themselves establish the entry SCC premise after
interleaved Value replay/extrusion and later zero-product restoration.

The precise open obligation is: for every authentic successful restoration
prefix immediately before an Effect child starts, no distinct retained Value
parent/copy pair has become strongly connected since the last completed Value
drain. A completed Value drain settles its queue/dirty intrusion to a fixpoint;
the missing induction step is preservation across **zero-product captured
Value-bound insertion**, including parents created by earlier restoration
children. No source expression realizing its failure was found in this static
audit. No proof of its impossibility was found either.

## Small synthetic discriminator, not source evidence

Two Value rows suffice to refute “empty queue plus zero opposite count prevents
Value work in an Effect drain”. Let `P` be an original, `C` its distinct retained
positive extrusion copy, with identity relation fibers and no current completed
pair suppressing the replays. Store:

| Owner | Lower bounds | Upper bounds |
| --- | --- | --- |
| P | none | C, UnitNegative |
| C | IntPositive | none |

The graph has `P→C`, and the queue is empty. Insert a positive lower `P` into
`C` through the restoration owner. Its opposite count is zero, yet the
dependency graph now also has `C→P`. Retire that zero-product operation, then
start an Effect `BottomPositive <: EmptyNegative` drain. Global settlement
merges C into P and replays the merged Int lower against the Unit upper.
With the stated fibers/current-memo premise, dispatch records a pending
Int/Unit witness, completion retains it, and the cleared Effect loop reports
no Value witness at that cause.

This is a **conditional synthetic transition derivation**, not an executed
test or an authentic source witness. Directly installing these storage bounds
and parent provenance does not prove their coexistence is produced by ordinary
source inference. In particular, the last bound redundantly stores `P <: C`
at the opposite physical owner from the existing `P` upper `C`; ordinary
`candidate_apply_value` selects its row owner by levels (`:814`), while fresh
restoration preserves a captured side. A genuine witness must supply that
captured predecessor and its complete history. The state is minimal in row
count for a distinct parent/copy merger; no minimum source size is claimed.

## Evidence, resources, and next action

Method: bounded static reads (`rg`, `sed`, `cat`) plus the preceding conditional
derivations. No checker or external oracle was used; the conclusions share the
actual compiler transition rules and do not independently prove language
semantics. No seeds, enumeration range, mutation run, Cargo process, tests,
probes, compiler edits, or Git mutations. One read-only baseline re-pin command
was used as required by the packet. Reads were serial/brief; no heavyweight
process. Peak CPU/RAM and exact elapsed wall time were not measured; the
30-minute packet limit was not used to launch further searches.

Unverified scope: authentic restoration reachability, source rejection,
later witness rescue, publication/production consumers, suspension/recovery
histories, and the complete soundness/principality obligations. Even an
authentic witness at this seam would establish a diagnostic bug; it would not
prove or refute the entire source-rejection theorem without its consumer bridge.

Recommended next action: assign the owning freshening proof lane the exact
zero-product SCC-preservation obligation above, using captured bound orientation
and prior child extrusion as the induction boundary. Do not repeat a saved-queue
probe or promote the conditional exclusion to source impossibility.

## Commit packet

- Lease/changed path: `notes/progress/2026-10-11-effect-drain-value-witness-reachability.md` only.
- Baseline: `74e027c9f8cbf37cb11acf4ce4a53b9613dbfedb`.
- Direct source SHA-256 snapshot: lib `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94`;
  context `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987`;
  extrusion `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0`;
  intrusion `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0`;
  scheme `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1`;
  effect `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df`;
  source `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49`.
- Dependency changes: none observed during this packet; primary must compare
  these frozen hashes with the pinned revision before integration.
- Review: producer output, independent review pending; writes stopped at handoff.
- Checks: exact owning branches read; dependency hashes captured/rechecked;
  no executable verification authorized or performed.
- Proposed commit: `research: trace Effect-drain Value witness reachability boundary`.
- Shared-record deltas left to primary/curator: preserve parent rejection gate
  OPEN; record clearing order and saved-queue exclusion; add the zero-product
  restoration SCC-preservation premise without claiming source closure.
