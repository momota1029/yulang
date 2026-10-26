# Shared Context publication, processing-owner readback, and committed histories

Date: 2026-10-26. Baseline supplied by the primary:
`820ed79a8891e72c85280a5e0313e57fb05f3b73`.

Status: kernel-checked constructive supplier; independent review pending.
The original **CONTEXT-COMMITTED-READBACK** application and original complete
inference soundness remain OPEN at the native interpretation boundaries below.
This note does not narrow their source language, complete keys, scoped demands,
or semantic requirements.

## 1. What this construction supplies

`NativeContextReadback.lean` joins the accepted full local Context construction
to the accepted immutable-occurrence drain model. It constructs one history
containing the actual distinction between early discharge publication, memo
admission, and completed Dispatch. Its final readback follows a queued
occurrence through its computed canonical processing relation and retained
Derived edge to a constructed body. A duplicate can refer to an active owner;
the history proves when that owner subsequently has a sealed body.

No constructor assumes `ClosedAt`, `InstalledAt`, full Context coverage, a
completed-owner callback, or the semantic validity of a memo. Neither pending
coverage nor `discharged` implies completion. The public quiescence roots derive
the required owner/seal facts from the shared history and actual clearing cuts.

The construction is parameterized by one `NativeContextExpansion.Tables`
interpretation. This is an explicit application boundary. The checked lifetime
example in §7 proves why that interpretation cannot silently be held fixed
across arbitrary native rollback and raw-ID reuse.

## 2. Complete represented data

The state contains the native drain projection, Effect and Value representative
maps, generation, append-only relation/task interpretations, per-occurrence
Transport routes, checked/published/ready Context stages, the discharge table
and its post-check Context map, active residual owners, the typed-pair memo,
sealed body recipes, completed-occurrence receipts, Derived edges, and a
settlement-session marker.

`Relation.effect` retains all fields of the admitted Effect `Key`: both
endpoints, stored Context, optional source-set identity, and transformer.
Effect scoped demand is absent because native admission rejects a present
demand. `Relation.value` retains both Value identities, stored Context,
sources, transformer, and the complete optional `ScopedDemand` record:
original Call, use instance, root, output scope, and input route. Transport
preserves these payload fields while computing canonical endpoints and the
exact stored-versus-post-check Context branch.

The task remains the immutable raw diagnostic pair. The drain's `Work` retains
its occurrence serial and Replay ticket, while the frame's `processing`
relation can change. Memo lookup is indexed by the processing relation plus
its complete key; the latter is redundant interpretation data, not an
endpoint-only cache. Native relation interning is unique and immutable within
one forward lifetime. The `intern` event records the new-slot, uniqueness,
and whole-relation admission guards.

A `Route` retains the original work item, canonical processing identity,
original complete relation, representative maps at Transport, and any actual
earlier discharge prefix. Its target and Derived edge are computed functions.
An original discharged prefix remains attached to the original obligation even
when the new processing relation carries only its residual Context.

## 3. Finite native event obligations

The source locations refer to the frozen bytes recorded in `inputs.json`.

| Native owner and cut | Constructed event or theorem |
| --- | --- |
| `candidate_context.rs:3062–3073` | `Relation.valid` and `Step.intern`: nonzero-transformer Effect self-relations rejected; Value transformer zero; Effect demand rejected by the admitted representation. |
| `candidate_context.rs:3767–3785` | `Step.transport`, `makeRoute`, `Route.target`, `Route.derived`: actual raw work owner, canonical-pair agreement, exact interned target, unchanged-pair identity branch, and Derived dependency. |
| `candidate_context.rs:3800–3868` | `prepare`/`prepareParsed`: unchanged parser and ordered `checkFilter` calls from the frozen local module, with all Effect operand, retained-bound, source, transformer, and callback-success guards. |
| `candidate_context.rs:3870–3885` | `Step.publish` first reserves and records the checked prefix and post Context; `Step.sample` separately admits successful publication sampling into the ready stage. No seal is created by either event. |
| `candidate_context.rs:3839–3840` | `Step.contextCached`: same complete discharged owner, successful current parse, nonempty filter prefix, canonical pair and self-relation guard. `cached_parser_readback` derives the repeated parse result independently of fuel. |
| `lib.rs:13507–13518,14443–14456`; `candidate_intrusion.rs:423–455` | `pairCurrent`, `Step.admit`, `Step.duplicate`: the native completion memo is written at admission, before residual execution. It names an actual active occurrence or its later seal. Raw aliases only mark the processing relation when the admitted raw pair is canonical. |
| `lib.rs:14344–14420` | `Step.finish`, `Step.duplicate`, `Step.valueExit`: the actual current-work clearing cut. `finishPrefix` computes the consumed branch or the exact residual application before creating a seal. |
| `candidate_intrusion.rs:568–599`; `lib.rs:14308–14339` | `beginSettlement`, `merge`, `endSettlement`: empty worklist and no current task at entry; work may be queued by an earlier merge inside the same loop. Administrative frame changes are barred while that session is active. |
| `candidate_context.rs:2076–2160`; `candidate_effect.rs:338–389`; `candidate_intrusion.rs:234–245`; `lib.rs:9646ff` | The joint journal projection in §6. Actual table lifetimes and the concrete distributed native erasure still require §7. |

The native drain projection permits administrative events only when the total
number of processed occurrences is unchanged. The preservation proofs inspect
every `NativeDrainOwnership.Step` constructor. Clearing Dispatch increases that
count and therefore must pass through the refined finish/duplicate/Value-exit
events. Moving a frame's processed list into a return receipt preserves the
count. This is a raw event guard, not an assumed coverage property.

The successful event grammar is an ownership projection; it is not asserted
to be a bijective encoding of every Rust micro-interleaving. Preflight operations
that do not alter its fields can stutter. Native failure/cancellation must map
to the same journal, rather than continuing an independently chosen control
history with a separately chosen Context history.

## 4. Constructed readback, including active duplicate owners

`staged_decompose` and `staged_expand` show that preparation followed by successful
residual completion reconstructs the frozen computation. For a fresh execution
with the same callback snapshot and successful publication,
`fresh_body_is_frozen_built` directly constructs the accepted module's `Built`.
For cached prefixes, `PrefixRecipe` retains their earlier actual computation
and explicit carrier transport; `BodyRecipe` adds the later computed consumed
or residual branch. These recipes have no completion-from-memo constructor.

`step_invariant` proves four related facts from their owning transitions:

1. Every admitted residual owner is still the current work of a real frame or
   has a seal whose complete key matches it.
2. Every memo names that actual owner and the same complete processing identity.
3. Every completed occurrence receipt names its real owner with the same key,
   or retains the exact successful Value Context forwarding request.
4. Every processed occurrence, including one moved into a return receipt, has
   a corresponding Context receipt.

The proof does not require a prior seal when a duplicate exits. A fresh owner
is introduced only by admission while its frame is current. A fresh seal is
introduced only by the computed residual/consumed completion. Other native
control transitions cannot silently remove the owner. At a no-current cut the
live alternative is impossible, so the seal is derived.

`Witness.active_memo_run` is a concrete run from the empty initial state through
interning, enqueue, dequeue, Transport, Context and memo admission. It uses a
nonzero transformer and a nonempty optional source identity.
`Witness.active_memo_is_not_completed` computes that the memo exists, its owner
is live, and the seal list is empty. This is a control/construction witness,
not an accepted source program or a semantic counterexample.

`actual_discharged_prefix` derives that every published prefix came from fresh
ordered checks and is nonempty. `run_references` follows those records through
Transport and all subsequent stage/receipt references, preserving the actual
Derived edge. `quiescent_original_context_readback` consequently returns, for
every issued occurrence, its completed receipt, canonical processing-body
recipe, prior original checks, and retained dependency. The original key is
not left at a pending graph vertex while an unrelated canonical key is sealed.

`resolved_body_whole_child_provenance` covers every child of every check and
every residual continuation, including transported recipes. Each child retains
its own source-derived Context, the full parent's source and transformer
payload, and the nonzero-transformer self-relation guard. It does not replace
those fields by endpoint-only equality.

## 5. Exact settlement horizon and semantic boundaries

A top frame with no current task and an empty worklist can be inside a
synchronous drain whose outer frame still owns an admitted residual operation.
It is incorrect to demand an already sealed body for every such inner-cut
memo. `settlement_owner_readback` gives precisely a seal **or the actual active
outer frame and owner occurrence**. It supplies no queued or abstract pending
fallback. `merge_session_has_actual_cut` derives the no-current working frame
throughout the entered settlement session; it does not require the worklist to
remain empty after an earlier merge queues work.

At a true no-current cut, `memo_body_at_cut` and `effect_receipt_original_body`
derive the seal. At empty queue and empty stack,
`quiescent_replay_readback` also obtains the exact diagnosed ticket receipts
from the same control projection. Replay tickets retain their original admitted
relations and operation births; Transport does not rewrite those immutable
occurrences.

The `Receipt`/return lists are history-derived ghost records of those actual
cuts. They are not read back from the optional native
`source_drain_completions` vector. In `candidate_context.rs:2177–2184`,
`record_source_drain_completion` can return early when observation allocation
fails while inference remains successful. Native `Ok` therefore does not imply
that optional evidence vector contains a completion receipt. None of the
theorems here makes that implication.

The supplied body is a completed **construction recipe** of its processing
owner, with explicit snapshots and carrier recipes. It is not a proof that its
leaves denote semantic subtyping or that diagnostics contain no conflicts.
Successful `applyEffect` may retain conflict leaves. The model records merge
representative updates and settlement ownership; it does not reconstruct the
entire physical bound store or assert that a historically sealed body's raw
carrier is already the final representative. Applying the frozen
`NativeContextExpansion.mergeGraph`/`Body.transport` to the same actual merge
and bound-attachment history remains part of native carrier/semantic readback.

Value Context is handled without dropping its full request. The clearing cut
can follow any actual structured Value continuation, but this packet proves
only the exact Context forwarding result. Function, Tuple, Record, Variant,
extrusion, method/Call meaning, and their complete source-scoped interpretation
remain with their concrete dispatch owners. The primary's separately leased
Value-port packet is not imported here.

Likewise, local callback success and full child key construction are represented
by the frozen `Availability` interface. The Rust-to-event bridge must connect
each actual successful child enqueue to the corresponding immutable `Work`
and Replay transfer in this same history. The current theorem proves readback
for **every actually issued occurrence**; it does not invent an issued occurrence
merely because an availability Boolean is true. Its exact suppliers are
`candidate_context_admit`, `candidate_check_effect_operand`, and `enqueue_item`
(`candidate_context.rs:3458ff`, `candidate_effect.rs:1237ff`, `lib.rs:15223ff`).

## 6. One joint committed projection

`Transaction` updates one joint journal cell with a concrete `Step` result.
The old cell is obtained by actual journal lookup. It contains the complete
Context/drain/memo/receipt state, so no independently selected sub-history can
substitute a different owner. `Attempt` allocates a distinct journal birth;
`cancelled_attempt_birth_not_reused` proves cancellation retains a later clock
even if numeric frontiers are reused.

`Committed` includes successful commit and cancellation of those concrete
attempts. `committed_readback` derives a single surviving forward `Run` from the
initial state. Cancellation uses `NativeExecutionHistory.cancel_table_exact`
for the whole cell, restoring publications, owners, seals, memo and control
together. `committed_quiescent_context` then applies the original-occurrence
readback without taking a separate forward run or completed-body premise.

The one cell is a **joint proof projection**, not a claim that Rust implements
one physical snapshot or fully restores every internal counter/capacity.
Mapping the actual distributed native journal to that projection must preserve
the relevant semantic fields and constructor lifetimes. The generic exact
snapshot theorem by itself does not establish that mapping. No additional
native rollback requirement is imposed beyond the authoritative successful
inference and safe publication contract.

## 7. First remaining owner: TABLES-LIFETIME-READBACK

The required next construction is source-determined versioning of all five
`Tables` components. A generic equality assumption between two whole tables
would forbid genuine fresh allocations and would leave the same owner open.

| Table or dependent identity | Exact native construction/rollback owner |
| --- | --- |
| Context nodes, all six constructors | `State::context`, `candidate_context.rs:2630–2655`; child assertions at 2786ff; node/key truncation at 2141ff. Context IDs are `contexts.len()+1`, with zero reserved for identity. Function ports and replay use this interner at 3533ff and 4042ff; fresh renaming uses 1556–1689. |
| Weights and exact allowed input | `source_weight`, 2734–2758; `validate_payload_view`, 1729ff; weight rollback at 2121ff. Weight IDs are `weights.len()`. Preserve the copied allowed sequence, boundary, owner, position, zero words, and source attachment provenance. |
| Views, closed weights and tails | `candidate_signature_view`, `candidate_effect.rs:859–909`; copy/remap at 1155–1197; Effect-algebra checkpoint/rollback at 313–389. The view index is reserved from `views.len()` before `source_weight` runs; the weight can exist before the matching View is pushed. Closed weight exists only for the appropriate closed view. |
| Contributions | `candidate_effect_contribution`, 1213–1236: index from `contributions.len()`, actual effect/origin, `instance=id`, then resource sampling; rollback truncates contributions. |
| `prefixIdentity` interner result | `candidate_context_source`, 3361–3372: actual closed-allowance weight and the nonzero result of interning `PrefixLeft(weight,Identity)`. It is an event result of the Context interner, not an immutable independent total array. |
| Complete relation, source and scope references | `relation_with_scoped`, 3062ff; source sets and relation-key rollback at 2145–2160; scope interning/flow rollback must retain full transformer and demand references. |
| Common failure/commit boundary | Context checkpoint/rollback 2044–2160, Effect-algebra checkpoint/rollback 313–389, intrusion completion restoration 234–245, and `lib.rs` begin/finish/rollback route owners 9271ff/9489ff/9646ff. |

The minimum useful transport statement should be indexed by a concrete
constructor/extension/cancel trace and either allocation-stamped handles or
the exact successful access footprint. For each still-live observed handle,
its allocation birth, payload and dependent child handles must read back to
the same constructor record at the later callback cut. New allocated slots
are allowed. A meaningful failed lookup must stay attached to its observation
version; a later `None → Some` allocation cannot be erased by pretending the
earlier observation queried the later table. Prefix-interner return IDs need
their actual allocation/reuse event, including absence and subsequent creation.

From that statement, transport the actual `scanStep`/`ScanRun`,
`weightValid`, `sourceAvailable`, `effectTables` operand lookups, `prepare`,
`finishPrefix`, and `valueContext` computations. Correlate the tables used at
Context checking, publication, cached parsing, residual Dispatch and rollback
with the same joint history. The weight-before-View window must be represented;
it is not legitimate to assume every intermediate weight already has a valid
published View. Failed preparation/publication must be erased or safely
terminated through the owning common route.

`LifetimeBoundary.two_successful_parses` gives a precise checked obstruction to
one unversioned interpretation: raw Context slot 1 contains
`PrefixLeft(weight 1,Identity)` in one lifetime and `Swap(Identity)` after reuse.
The parser results are respectively filters `[1]`, residual `0`, and filters
`[]`, residual `1`. `no_single_raw_table` proves that one lookup function cannot
represent both constructor contents. Native `context` does not fold the Swap
constructor; rollback removes the prior interner entry and truncates the vector.
This is a source-constructor/interpretation obstruction, not a refutation of
inference soundness or a claim that a particular source program is accepted.

## 8. Verification and handoff

The module imports only frozen `NativeContextExpansion`,
`NativeDrainOwnership`, and `NativeExecutionHistory`. There are no production,
configuration, dependency, root-import, expected-output, Git, or sibling edits.
The complete final source, every failed/successful snapshot, complete originating
declaration types and transitive axiom census, dependency hashes, commands,
resource receipts, and named roots are retained in the owned
`context-readback-r4` scratch packet. The producer handoff records the final
counts and hashes. No originating project axiom, proof hole, native-evaluation
bypass, or unapproved axiom is admitted.

Fresh independent review and the primary's integration remain separate from
kernel acceptance. The original parent remains open until the versioned native
constructor/event bridge, carrier/diagnostic interpretation, and remaining
Effect/Value/source semantic owners are supplied for the original full scope.
