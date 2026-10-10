# Nonterminal typed-drain owner seam

Date: 2026-10-11
Status: implementation plan under the approved private suspension contract; no code gate is closed.
Baseline: `e0c68c6b67bfc351631e12a8adfad7dbc5c6f4d5`.

## Authority and evidence

The private candidate suspension contract §§3 and 6 requires an owned typed
drain continuation and exact route rollback. The acknowledgement-prefix proof,
source audit, finite falsifier, owner-composition proof, and owner test contract
are conditional research evidence; they do not claim that the current compiler
can resume a retained nonterminal drain.

The pinned implementation has no such resume entry. A fresh synchronous drain
creates and runs one frame; route entry requires empty typed work and diagnostic
scratch; route rollback clears those session collections. Replay `Ok(())` can
also denote queued but unfinished children, so it cannot authorize restoration
or local parent advancement after execution becomes interruptible.

The proposed whole-workspace replacement strategy was rejected on structural
cost grounds. Copying or reconstructing a queue of `Q` items and diagnostic
frontier of `D` entries per resumed route adds `Θ(Q + D)` work and retained
capacity per route, potentially multiplying that work by resume count. The
performance audit found this material without needing timing samples.

## Bounded implementation direction

Separate private start and resume entries into a saved-stage drain driver. Start
seeds/enqueues once. Resume owns the topmost frame and its exact current item,
stage, Function cursor, transition total, ordered queue, diagnostic frontier,
and processing scope; it must not reset or recreate them.

Use per-mutation undo for workspace state, reserving undo and target capacity
before every queue push/pop, diagnostic admission, frontier clear, or workspace
transfer. Preserve old allocations only on actual growth, and restore them by
infallible moves after reversing later mutations. Keep diagnostic completion
atomic: retain its input delta/index state, while reverse-edge/SCC completion
scratch stays call-local. Journal diagnostic memo/error/publication effects
within that atomic route boundary.

Before any resumed saved-stage effect, pop, append, or direct Function
admission/enqueue, prepare the complete acknowledgement suffix
`[completed_acks, replay_acks.len())` against the current route journal. Advance
`prepared_acks` only after each exact position has undo. Preserve terminal
one-ack preparation and repeated operation occurrences.

Replay parent, restoration parent, and Local parent advance only from an
explicit child-complete receipt. An unfinished result preserves the exact
active child and parent cursors. Keep nested workspace transfer unsupported
until an actual caller and its parked-workspace ownership are demonstrated;
this limit must leave existing synchronous routes intact and must not be
reported as general suspension or §7 closure.

## Review and verification constraints

Pre-write spec audit found this direction consistent with §§3 and 6, subject to
three closure points: exact whole-route workspace restoration, completion-
distinct parent handoff, and a complete atomic diagnostic boundary. It also
requires preserving existing terminal partial-ack/removal rollback, empty/final
batch, Function ordering, and queued-versus-consumed tests. No expected outputs
or semantic test claims may be changed.

The implementation has material queue/map undo and peak-accounting risk. Count
active, parked, growth-retained and clear-retained storage; do not clone
untouched workspace on each route. Exercise failure after partial queue/index
mutation and after a later acknowledgement reservation. A counted failpoint is
needed to target the second prefix reservation; the current boolean failpoint
cannot establish that case.

Selected mode: M2. One implementer owns the connected files `lib.rs`,
`candidate_context.rs`, `candidate_context_tests.rs`, `candidate_extrusion.rs`,
and `candidate_scheme.rs`. Primary owns all builds/tests and Git. Closure review
must cover continuation/replay ownership, exact rollback, §§3/6 conformance, and
the structural performance risk within the reviewer budget. No broad suite or
timing matrix runs at this intermediate gate.

## Stop conditions

Stop the implementation if any workspace mutation lacks journal-before-mutate
ownership, rollback needs allocation, workspace identity is reused while undo
still references it, diagnostic completion can suspend inside the claimed
atomic phase, or an unfinished child can advance a parent. Do not add a time or
size rejection cap. Production certificates, external incidence interleaving,
withdrawal/recomputation, resumable SCC publication, and authentic §7 source
recognition remain separate open gates.
