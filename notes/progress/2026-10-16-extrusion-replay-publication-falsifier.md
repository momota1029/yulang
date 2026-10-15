# Extrusion replay descendants versus source publication

Status: independently reviewed bounded static falsification/owner audit. No
source-qualified counterexample found; H2 and the original lifecycle parents
remain OPEN. Baseline supplied by primary: `231a7d2bb`, native `bf056` stable.
Exclusive lease: this note only. The independent constructive completion note
was not read.

Fresh compiler-referee `ordinary_carrier_semantic` reviewed this exact bounded
source exclusion CLEAN at producer SHA-256
`5b930c74dc14000081458f097dcc1e827b35e4196b61e640d19d01f8c2041f86`.
The reviewer separately accepted the [constructive operational bridge](../theory/2026-10-16-extrusion-replay-capture-completion.md).
No source-qualified premature-publication witness was found; this is not a
universal no-counterexample, duplicate-soundness or source-context theorem.
Primary consumed the operational leaf only; original H2/U remain OPEN.

## 1. Question, authority and acceptance condition

Attack the necessary lifecycle property: after copied-cut replay admits
necessary descendants, a dependent FreshUse/publication must not reuse an
incomplete result unless the unfinished state remains explicitly owned and
invalid for that reuse. Outstanding unrelated FIFO work, a provisional capture,
or a not-yet-generated source constraint is not a counterexample.

Authority: top-level inference principles §§1–4; contextual attachment/admission
design §4–6; contextual residual-lineage selection; private suspension contract
§§3–5. Successful suspension with owned deferred state remains permitted. No
new rule requiring all constraints solved before generation/capture is assumed.

The independently reviewed
`2026-10-15-extrusion-initialization-replay-invariant.md` §§1,3,7 establishes
exact fiber-product queue admission, not descendant completion. This audit
asks whether actual source control flow can publish around its descendants.

Claim class: bounded negative falsification evidence and actual-owner exclusion
of the proposed early-publication ordering. This is not a semantic theorem
that every omitted duplicate is redundant, every source cut is sufficient, or
every supported suspension/certificate generation is valid.

## 2. Authenticate the production extrusion entry

Static call-site search finds only two non-test calls of `candidate_extrude`:
the positive/negative structural-to-row rewrite arms in `lib.rs:12551,12564`.
Other direct calls are in test modules. The production arms execute inside
`dispatch_live_item`, under the active typed drain; they do not start another
source action or graph capture.

`candidate_extrude:305–386` installs/transports IncomingAllowance bounds,
finishes the structural work and parent group, then calls ordinary replay for
their saved installed keys. Replay with no provenance transfers children to
the current typed worklist. Structural dispatch subsequently queues the
rewritten Value (`lib.rs:12586–12590`). A Support expansion or further bound
replay may append a descendant behind that rewritten Value. This is a real
permitted ordering, not evidence of publication or lost work.

The distinction from the old private direct-extrusion fixture is decisive:
directly calling extrusion and opening another route before consuming its
queue was a test-only ownership violation repaired in the reviewed October 15
implementation checkpoint. No authentic source scheduling edge doing that was
found here.

## 3. Follow descendants through the actual drain

`constrain_live_item_with_inferred_entry` (`lib.rs:12079`) immediately selects
`run_candidate_typed_drain` for a candidate session. The latter loops
`step_typed_drain` until it returns a completion receipt (`:12282–12302`).
It has no successful early return for “children queued”.

At each Transport stage with no current item (`:12355–12387`):

1. An empty queue first triggers `settle_candidate_intrusion`.
2. The next actual queue item is popped and retained in the drain frame,
   including any replay acknowledgement.
3. No item and no intrusion dirty state advances to Diagnostics. A dirty
   state keeps the drain running.

Each item then passes actual context transport, context execution and dispatch.
Function dispatch has its own retained port/enqueue cursor; the source driver
does not run between its children. Descendants appended behind a rewritten
Value are therefore still reached by this same loop before source return.

Diagnostics (`:12423–12440`) runs after the worklist/dirty test, replays
conflicts and completes the diagnostic delta. Terminal processing
(`:12708–12769`) consumes retained replay acknowledgements before ReturnReady
can pop the drain frame. A replay acknowledgement is not transferred merely by
generating its child: `enqueue_item:12970–12994` records transfer only after
queue/evidence capacity preparation, and the drain owns completion thereafter.

`candidate_context_consume_replay_child` (`candidate_context.rs:3575–3608`)
explicitly distinguishes queued children from consumed children. With no
provenance, `ReplayDriveOutcome::Queued` leaves completion with the outer
drain. With provenance, the restoration adapter drives its child to a returned
receipt. No source publication is performed by either adapter.

This excludes the specific ordering “rewritten Value runs before descendant,
therefore the source publishes first”. It does not prove correctness of the
descendant's semantic operation or of arbitrary future dependency mutation.

## 4. Attempt duplicate, canonical and intrusion shortcuts

### Same-generation duplicates

`pair_is_current` (`lib.rs:11585–11596`) requires both a raw diagnostic pair
and completion of the **actual processing RelationId** at the current intrusion
generation. Relation identity includes pair, context, source set and scoped
flow (`candidate_context.rs:2569–2600`), rather than endpoints alone.

`mark_candidate_pair` (`candidate_intrusion.rs:352–384`) stamps a canonical
relation during admission, before all its descendants necessarily finish.
This stamp therefore is not a standalone publication certificate. For the
inspected synchronous source path, an identical queued relation may skip
redispatch while its first dispatch's consequences remain in the same owned
drain; publication still cannot overtake that drain. No concrete necessary
consequence was shown absent from both retained state and that worklist.

This audit does not claim universal duplicate soundness under dependency-only
lifecycle mutation. Intrusion generation alone is not the separate lifecycle
certificate required by the suspension/attachment policy.

### Raw canonical rewrite

An attempted shortcut was: admit a raw alias, stamp its canonical relation
current, then suppress the queued canonical child using an old canonical memo.
The actual owner blocks this mechanism. `mark_candidate_pair` stamps completion
only when `key == candidate_context_pair(key)`; a raw alias receives diagnostic
provenance but does not complete its canonical relation. The canonical child
remains the semantic owner (`lib.rs:12485–12492`). Earlier diagnostic children
are retained when a memo is replaced (`:13086–13100`); they are not cleared by
the empty new diagnostic entry used at rewrite.

### Qualified intrusion

`merge_candidate_rows` (`candidate_intrusion.rs:535–610`) copies both bound
sides/origins, canonicalizes bound evidence, increments the intrusion generation,
marks dirty, reopens the root diagnostic and schedules ordinary replay at the
merged owner. Thus old-generation completion stamps fail `pair_is_current`.
The typed drain revisits intrusion after an empty queue before returning.
No static path was found that publishes directly from a merge callback.

This is control/generation coverage, not a proof that every qualified merge's
semantic consequences or every same-generation certificate invalidation is
complete. The old restoration live-index issue also remains separate: this
audit does not replace the selected saved-count/live-index behavior with a
claim that every initial opposite is visited once.

## 5. Authenticate source publication and dependent reuse

An actual source example already present in
`crates/yu-solver/tests/candidate_effect_annotation.rs:121–131` is:

```yu
act E
my value = { my local x: int -> [E] int = x; local }
my accepts: int -> [E] int = value
```

Its test asserts candidate acceptance; the adjacent F-only boundary case
asserts a conflict. These assertions were read, not run. The source HIR/action
owners authenticate the relevant ordinary Lambda/local annotation/Install,
Local Name and module-use schedule. This fixture is **not** claimed to reach
every IncomingAllowance copy or the private two-cut observer state.

The actual schedule/publication edges, independently of that missing exact
cut-reachability claim, are:

| Owning edge | Why the currently generated descendant queue cannot be bypassed |
| --- | --- |
| `step_candidate_source:1337–1345`, LocalAnnotation construction | Construction's source inequalities use synchronous constrain/drain calls. Stage changes to PublishLocal only after construction succeeds. |
| `step_candidate_source:1311–1317`, PublishLocal | Checked source wait/registration precedes this branch; publication installs the retained exposed root. It does not resume while a child action is still on its synchronous stack. |
| `execute_candidate_action:1348–1383` | Fact/ValueConstraint/Candidate/Lambda/annotation constraints and Module/Local routing use their actual `?`-returning owners. The action cursor advances only after return. |
| `install_candidate_local_term:1480–1500` | Stores live root, boundary and region; it does not freeze a graph or assert that future source constraints were solved. |
| Local Name routing `candidate_scheme.rs:1535–1537` | Recaptures the live local root before preparing its fresh use. Restoration completes before its bound cursor advances; the final Name link drains before `cursor.complete=true` (`:1664–1701`). |
| Module/SCC graph plan `:945–1011` | Executes all member schedules, then stages their captures, then publishes the component's graph slots. This is the implemented synchronous path, not a new general barrier. |
| Module use `route_candidate_graph:1058–1077` | Recaptures the stored graph's live root/boundary rather than blindly reusing its old bound snapshot. |
| Module FreshRoute `instantiate_candidate_graph:1428–1474` | Drives fresh bound restoration, performs the actual routed constraint, then records FreshRoute. Failed/unfinished work does not reach this success branch. |

Fresh restoration asserts idle-worklist entry and retains the accepted emission
and cursor (`candidate_extrusion.rs:699–716`). Its parent advances only after
the exact replay is Complete (`:758–770`). This prevents treating mere queue
admission as a completed restored bound on the inspected production path.

No all-source “solve everything before capture” rule follows. An installed
local may legitimately precede future source constraints. An explicitly owned
unfinished private frame may legitimately exist. Neither was used here as a
failure witness.

## 6. Result, limits and next action

Bounded exclusion: on the inspected non-test source execution path, necessary
descendants queued by extrusion cannot be overtaken by the next source action,
Local publication or recorded FreshRoute merely because the rewritten Value
was earlier in FIFO. The actual canonical-alias completion guard additionally
blocks the specific false-stamp/suppress attack above. No authentic invalid
dependent reuse was found.

Unverified: an exhaustive source witness for the copied-cut observer's exact
state; semantic soundness of duplicate omission; general attachment-certificate
generation/withdrawal; arbitrary dependency-only mutation; all resumable/cross-
component histories; exact residual eligibility; full H2/U and production
cutover. Private test methods that directly call extrusion, mutate fixtures or
step a child/source out of its authentic owner chain do not establish source
reachability. No such trace is presented as a counterexample.

Recommended next action: independent referee checks this bounded source-owner
exclusion and the exact early-completion/canonical guard. The constructive lane
can consume it to prove the owned-drain-to-publication implication, while
keeping semantic duplicate/certificate invalidation and authentic source-cut
sufficiency as their separately named obligations. No scheduler barrier or
implementation change is selected by this audit.

## 7. Checks and commit packet

Only bounded `rg`/`sed` reads, a leased Markdown write and dependency SHA-256
checks were used. No tests, builds, probes, Git operations, children, production
or shared-file edits. Existing test assertions and historical executable
observations are not fresh verification. One bounded 20-minute static packet;
CPU/RAM unmeasured. Producer output is unreviewed.

Exact changed path:
`notes/progress/2026-10-16-extrusion-replay-publication-falsifier.md`.
Baseline `231a7d2bb`; native `bf056` supplied stable. Proposed checkpoint:
`research: audit extrusion replay descendants at source publication`.
Primary owns independent review and task/theory/shared-record synchronization.

Frozen source SHA-256 snapshots (no dependency edited by this worker):

```text
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  candidate_extrusion.rs
199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070  lib.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  candidate_intrusion.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  candidate_context.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  candidate_source.rs
2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e  candidate_scheme.rs
```

All listed source paths are under `crates/yu-solver/src/`.
