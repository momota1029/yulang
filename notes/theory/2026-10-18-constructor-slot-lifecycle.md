# Constructor slot lifecycle at c881f5960

Status: candidate static source correspondence and local lifecycle argument;
fresh independent review NOT RUN. Author `/root/constructor_slot_lifecycle_proof`,
sole writer, descendants 0. Requested Sol/high; observed model/effort
UNKNOWN/UNKNOWN. Assignment `NPAIR-CONSTRUCTOR-SLOT-LIFECYCLE-20261018`, revision 1.
Sprint `npair-constructor-owned-replay-certificate-20261018`, revision 3,
contract SHA `c3e21e367b90a3d13165139cade12c2730f5a38ad3beb2ec1ec5a923c4fe1047`.

## Parent application and result

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN,
original conditions closed **0 -> 0**. Preserve the original contribution c
fixed before observation and its complete dependent declaration/reference/joint
assignments, provider/witness/residual presentation, worlds, contexts, typed
positions, occurrences, guards, continuations, interactions, demands and
futures. F1/FK1 remain independent. Adopted NPAIR §§2–4 and its adoption receipt
govern; P3/P4 and N-Transport remain obligations. A physical slot proves no At
association, contribution identity, general Call result or future completeness.

The inspected baseline supports **retained raw slot stability**: a candidate
emission that survives an ordinary route rollback still names the same raw
physical owner/lane/index and item until physical vectors are discarded at
finish. Intrusion redirects representatives and appends copies; it preserves
the original physical storage. Nontransactional candidate calls append and do
not truncate lanes. Route rollback pairs physical suffix retirement with
candidate evidence retirement through the saved context checkpoint.

This supports constructor readback as historical physical evidence for a
surviving emission, provided the actual addressed read is added and retained
with that emission. **The baseline does not perform that readback.** This audit
does not prove that the moving implementation emits an observation, that its
checker uses it, or that either numerical fixture succeeds. A new freeze-time
read is not required by the inspected ordinary lifecycle alone. Luna and the
fresh reviewer decide applicability to the changed implementation.

## Immutable inputs and method

Luna materialized read-only copies from baseline c881f5960 under
`/tmp/yulang-c881-immutable-audit/crates/yu-solver/src/`. This leaf verified their
SHA-256s before relying on them; no Git command was used. Initial working-tree
reads supplied navigation only; their four principal hashes also matched the
pins at monotonic_ns 307334229244889. All source claims below refer to the
immutable copies, never later shared edits. Line numbers refer to those bytes.

The mutation search followed the eight lane fields, their mutable aliases,
row creation, vector truncation/replacement/discard, the insertion callers,
and every production context/effect/intrusion rollback call found in those
owners. Test setup that directly edits private vectors is not an ordinary
source transition. Resource-probe discard is explicitly covered below.

## Append owners and checkpoints

`candidate_insert_bound_with_evidence` in `candidate_extrusion.rs:442–603`
canonicalizes its input owner/item once, admits a complete BoundKey, reserves
emission storage, journals the row, reserves capacity, saves the old lane
length, pushes, registers capture if requested, then emits the admission/slot
link. All eight arms use the same append macro at 447–466.

| Slot lane | Raw vector at its recorded owner | Stored item |
| --- | --- | --- |
| ValueLowerRow | bounds[i].direct_lower_rows | ValueRow ordinal |
| ValueUpperRow | bounds[i].direct_upper_rows | ValueRow ordinal |
| ValueLowerAtom | bounds[i].exact_non_variable_lowers | full ValueEndpointKey |
| ValueUpperAtom | bounds[i].exact_non_variable_uppers | full ValueEndpointKey |
| EffectLowerRow | effect_bounds[i].direct_lower_rows | EffectRow ordinal |
| EffectUpperRow | effect_bounds[i].direct_upper_rows | EffectRow ordinal |
| EffectLowerAtom | effect_bounds[i].exact_non_variable_lowers | full EffectEndpointKey |
| EffectUpperAtom | effect_bounds[i].exact_non_variable_uppers | full EffectEndpointKey |

Positive polarity selects Lower; Negative selects Upper. The Row/Atom choice
comes from the actual item enum. The raw row owner is saved in PhysicalBoundSlot,
not a pointer into a Vec allocation. Capacity growth therefore preserves this
address interpretation.

All candidate physical append routes converge here:

- Ordinary candidate Value/Effect propagation: `candidate_apply_value:844–873`
  and `candidate_apply_effect:876–899`, through `candidate_insert_bound:432–440`.
- Extrusion source link: `candidate_extrude:124–128`; copied selected bounds and
  incoming allowance cuts: 308–333 through `candidate_insert_copied_bound:416–430`.
- FreshUse: `candidate_scheme::begin_candidate_fresh_bound:1703–1749` through
  `candidate_begin_bound_restoration:695–714`. Module use goes through
  `freshen_candidate_graph_core:1406–1425`; local use through
  `step_candidate_local_use:2008–2022`.
- Qualifying intrusion: `merge_candidate_rows` in `candidate_intrusion.rs:520–600`
  copies both sides through `candidate_insert_copied_bound`, then transfers
  actual origins/fibers. Its 555–556 comment and 557–582 body explicitly keep
  physical source storage intact. Forest changes at 593/600 redirect row
  representatives without clearing or rewriting either lane.
- Signature/effect construction: `candidate_signature_effect` in
  `candidate_effect.rs:1704–1833`, inserts through the same owner at 1722,
  1753–1761 and 1824–1832.

The physical owner does not require an active route transaction. Its row
journaling functions return Ok immediately when `route_journal` is None
(`lib.rs:9331–9338`, 9380–9387). In particular, source schedule actions in
`candidate_source::step_candidate_source/execute_candidate_action:1457–1508`
can invoke constraint/signature constructors directly. This is why a proof
assuming every insertion is transactional would be invalid.

Module `route_incoming` explicitly uses `with_route_transaction`
(`lib.rs:16658–16674`); local `route_candidate_local_run` explicitly begins and
finishes its transaction (`candidate_scheme.rs:1846–1910`). Source actions that
invoke them receive those inner boundaries; the enclosing source schedule
does not supply one universal rollback boundary.

The legacy physical appends are separately owned by `lib.rs::apply_value_task`
(13925–14181) and `apply_effect_task` (11815–12030). They journal before each
lane append, but emit no candidate physical evidence. Their entry guards
13929–13932 and 11820–11823 return to candidate handlers whenever candidate_graph
is Some. They cannot justify a candidate certificate and do not supply an
alternative mutation of an already certified candidate slot. Row creation at
10137/10153/10172 and fresh row creation at 10238–10285 append default rows.
Candidate state is initialized by `try_new_candidate` at `lib.rs:10216–10221`,
before execution; `start_candidate_graph` at `candidate_scheme.rs:1040–1058`
is the state replacement owner. Reinitializing it inside an already running
route is not an ordinary production call and is outside the same-session-state
identity used by the argument. A future such caller would invalidate the audit.

## Removal, reuse and evidence rollback

`begin_route_transaction_for` asserts that no route journal is already active
(`lib.rs:9054–9055`). At 9205–9220 it saves `intrusion.begin()` and the physical
row counts without an intervening solver mutation. `journal_value_row` and
`journal_effect_row` save all four lane lengths on the first mutation of each
preexisting row. A row born after the checkpoint needs no individual undo:
the outer row vector is truncated instead.

The complete retirement chain is:

1. `rollback_route_transaction` takes the journal; at `lib.rs:9463–9464` it calls
   `intrusion.rollback(undo, ...)` when the saved candidate state exists.
2. `candidate_intrusion::State::begin:121–143` saved the effect checkpoint;
   `State::rollback:145–146` invokes its rollback. This restores forest state
   separately; it does not edit physical lane contents.
3. `candidate_effect::State::checkpoint:260–279` saved the context checkpoint;
   `State::rollback:281–282` invokes context rollback.
4. `candidate_context::State::checkpoint:1807–1836` saved EvidenceCheckpoint;
   `State::rollback:1877` invokes BoundEvidence rollback.
5. `BoundEvidence::rollback:584–606` restores group logs/maps, removes later
   snapshots/recipes/transforms, and truncates admissions/emissions to their
   saved lengths. Emissions are otherwise appended by `emit:749–755`.
6. `lib.rs:9524–9559` truncates all four lanes in every journaled Value/Effect
   row; 9568–9576 removes newly born rows and their companion metadata.

These are the production physical lane/row retirement sites found in the
inspected owners. Successful transaction commit only discards undo and commits
retained operations (`lib.rs:9286–9315`); it does not compact physical lanes.
`rollback_workspace` mutates worklists/diagnostic storage, not bound lanes.
Context/effect/intrusion rollback themselves do not truncate physical lanes;
their production invocation chain above reaches the route owner that does.

An error during rollback can occur before physical truncation, for example
`state.refresh_bytes()?` at 9484, after evidence rollback. This may leave an
uncertified physical suffix. It cannot retain a post-checkpoint emission naming
a retired slot: that evidence has already been removed. This is a one-way
safety argument, not a claim of complete failure restoration or safe retry.

**Local lifecycle argument.** Immediately after a successful append, the new
slot contains the pushed item. Subsequent appends, reserve reallocations,
metadata changes and representative redirects preserve every existing raw
slot's contents. At a route rollback, each retained pre-checkpoint emission
was created before that checkpoint's row/lane lengths and therefore lies
strictly inside the retained physical prefix. Every post-checkpoint emission
is removed before any suffix/row retirement. A later append may reuse a
retired index, but the prior emission is gone. Induction over these actual
operations proves raw slot stability for each surviving emission in the same
live session. It does not make a cached bare emission ID safe across rollback
or across sessions: Vec IDs can be reused. Re-fetch the surviving record and
its complete admission/route identity; no caller-held retired ID is a witness.

## Nontransactional failures and first stronger-claim obstruction

There is **no source-found stale surviving slot counterexample** in the
ordinary transitions inspected. The stronger statement “every physical append
has an emission, and every failed insertion rolls both back” is false as a
source control-flow claim:

- At `candidate_extrusion.rs:465` the item is already pushed.
- With capture=true and an Effect upper Allowance having a tail,
  `candidate_register_capture_bound` at 596 enters
  `candidate_effect.rs:609–615`, then `candidate_capture_incidence:533–583`.
  Its allocation and sampling steps can return Err before emission at 599.
- With no active route journal, no automatic physical/evidence rollback is
  performed by this insertion. A physical slot and admission can therefore
  remain without an emission. This is a static failure branch, not an executed
  resource-failure fixture or a closed accepted-source counterexample.
- Sampling at 600 can fail after emission; both slot and emission then remain
  outside a transaction. Again, no preexisting raw slot changes.

An absent emission must fail authentication. A retained post-error record
does not establish successful source publication. `run_candidate` propagates
execute failure before finish (`lib.rs:10445–10458`), and synchronous source
execution clears its source frame on failure (`candidate_source.rs:1382–1391`);
neither fact supplies a general retry theorem.

## Freeze boundary and implementation handoff

`finish_observations(self)` at `lib.rs:17503` reads physical bounds for output
projections, performs accounting, and constructs FrozenInferenceData at
17753–17775. It transfers candidate_graph at 17760, not bounds/effect_bounds.
The untransferred vectors drop with the consumed session. Resource-probe
configuration can discard them earlier at 17686–17699; its live event owner
is released there. No further solving or row reuse follows that discard.

Thus constructor readback remains an accurate **historical observation up to
discard**, and can be retained after discard. A post-solve checker cannot claim
to read the then-absent vectors. The recorded raw owner must not be replaced by
its later canonical representative: intrusion deliberately leaves old storage
at the original row while logical fibers can move. Current canonical fiber
membership remains a separate check and is not implied by physical contents.

Minimal provisional TODO `NPAIR-SLOT-READBACK-LIFECYCLE-20261018`, implementation
owner `/root/constructor_replay_impl`: read the addressed vector/index in each
of the eight insertion arms, reconstruct its complete raw BoundKey, compare
it with the admission, and retain a fixed-size observation with the emission.
Reject absent/out-of-range/wrong-kind/wrong-owner/wrong-side/different-item
records. Preserve route rollback by placing the observation inside the existing
emission rather than a separate registry. Compare the stored raw coordinate;
authenticate full route, source snapshot, admission and fiber independently.
Falsifiers: a retired record survives slot reuse, an earlier cached ID selects
a later emission, canonicalizing the stored owner reads a different row, a
wrong physical item authenticates, missing/replaced observation authenticates,
or any new source path mutates a surviving lane before discard. Intentional
pre-freeze mutation must be checked against the selected evidence phase; this
baseline lemma covers actual owner transitions, not arbitrary test corruption.

Luna TODO: obtain fresh review of this source argument and the changed physical
owner together; re-establish the mutation inventory for changed bytes. This
author is a complementary contributor and cannot certify the combined result.
Parent TODO `NPAIR-P3P4-DEPENDENT-TRANSPORT` remains with original Operation/Call,
capture/generalization/extrusion/qualifying-intrusion/effect-consumer owners:
prove fixed-c/At, all reached and future contributions, independent lineages and
full dependent transport. The local lifecycle result supplies only the selected
physical-evidence premise of the existing constructor certificate.

## Reuse, pins and resource receipt

Reuse the prior constructor owner map only for its actual topology, eight-lane
meaning and conditional input-identity argument; its fresh map review does not
review this lifecycle argument. Reuse the earlier CLEAN replay/fiber proof only
under its actual snapshot/physical/fiber/consumer hypotheses. Reject universal
transactionality, emission-totality, canonical-owner substitution, cross-State
bare IDs, and tests of assumed transitions as source-generation proof. Compiler
dependency authors are UNKNOWN; this leaf claims none of their authorship.
Prior map author `/root/constructor_replay_proof`; prior fiber proof author
`/root/replay_fiber_consumer_proof`; source proposal author
`/root/negative_formal_pair_proposal`; adoption/sprint authority Luna/user.

| Direct dependency | SHA-256 |
| --- | --- |
| rev3 sprint contract | c3e21e367b90a3d13165139cade12c2730f5a38ad3beb2ec1ec5a923c4fe1047 |
| notes/theory/2026-10-18-constructor-owned-replay-certificate.md | 9d465453a4433905813a8db84ba062abf324c75cced1879faffef2b291c03f2f |
| notes/theory/2026-10-18-replay-fiber-consumer-certificate.md | 691a537b441bff0947b47886f423199e9558740778d81e50858eedd85e3e3614 |
| notes/design/2026-10-17-negative-formal-pair-formation-proposal.md | 0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006 |
| notes/design/2026-10-17-source-formation-proposals-adoption.md | d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa |
| notes/design/2026-10-11-yulang-inference-top-level-principles.md | 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 |
| c881 candidate_extrusion.rs | 2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b |
| c881 candidate_context.rs | c0952a2c618bc01d7291f8c48c5e2012cffaa1c95491e2d026ff16a0831e0d12 |
| c881 candidate_scheme.rs | 9e548da9575d74a1da9ca8e70a70249eb3dc7a7c0f54f2cba5c525e0bfe1e73e |
| c881 lib.rs | ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1 |
| c881 candidate_intrusion.rs | 7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c |
| c881 candidate_effect.rs | 9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212 |
| c881 candidate_source.rs | 1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e |
| c881 candidate_scope.rs (navigation only) | 9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a |

Monotonic stages (ns): authority/ACK start 307304901194208; immutable source
audit start 307346463573192; source audit end/derivation start
307429150354266; derivation end/freeze start 307456319559568. Final freeze end
and handoff hash are in the external intake receipt. Cap 600s, Astra0; charge
the full grant conservatively, no remaining grant or rollover. Bounded file
reads, symbol searches and SHA checks only. One initial `python` command failed
because that executable is absent; `python3` supplied time/hashing. Combined
reads sometimes truncated; decisive owner branches were reread in bounded
excerpts. No tests, Cargo, solver execution, Git, external contact, code changes,
nested CLI or descendants.

Only written paths: this artifact and
`tasks/agent-loop/inbox/20261018-constructor-slot-lifecycle-proof.md`. No leaf
scratch files. The eight `/tmp/yulang-c881-immutable-audit/` inputs were created
by Luna, not this leaf. After final hash receipt this writer STOPs; fresh review
and central synchronization remain with Luna.
