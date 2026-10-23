# R346 — ordinary K0 replay coverage

Status: **frozen producer candidate, revision 1; fresh independent review required**.
Assignment `R346-K0-REPLAY-COVERAGE`; author
`/root/r346_k0_replay_prover`. Luna `/root` supplied the complementary source
census. No descendants. This is a bounded hand proof over pinned source, not
an execution observation, independent certification or production authority.

## Parent, quantifiers and exact result

The unchanged parent is the original Yulang2/Simple-sub source/native A/B
objective, with its original source domain and quantifiers. The immediate
supplier is audit N/D2 and `R345-N-REMAINDER`: temporal/fiber coverage of
ordinary bound replay. The original audit's N requires solution preservation
for an actual same-row-set propagation step; its I-work/source completeness
requirements are distinct. This packet supplies the particular ordinary
generation/ownership argument below, then applies the accepted R339/R345
entailment results at its actual consumers.

Use exactly authentic ordinary `ValidK0` of R336 rev4, L0 and R337 J. Quantify
over every finite successful prefix in that domain, every ordinary
`OwnerEmission` Value or Effect admission and fixed ordered replay input pair
`K=(kL,kU)` selected by its actual replay loop. For the covered interval fix
the existing kinded inference rows, representatives, endpoints and their
meanings. The successful-prefix boundary includes intermediate publications
of successful operations and continuing diagnostics; it gives no publication
or retry theorem for a resource-failed private attempt. No conflict-free,
acyclic, finite-solution, fair-scheduling or global-termination premise is added.

The candidate result is:

1. The two cursor loops visit exactly the disjoint product difference
   `newLower × allUpper ∪ oldLower × newUpper`, once per ordered pair of
   exact fiber identities. Duplicate physical endpoints do not multiply this
   fiber obligation; identical attached membership adds no fiber.
2. At successful generation boundaries every visited new exact dependency
   has an actual child slot. Every previously generated exact dependency has
   a source-derived earlier slot history, with live operation/queue/frame
   ownership until its exact terminal acknowledgement. In the authentic
   monotone ordinary history a *newly visited* pair cannot already have the
   exact dependency key. An old-key rescan has no newly visited pair.
3. Ordinary replay transfers the batch to the real typed worklist. It does
   not claim completion merely on `ReplayDriveOutcome::Queued`. Successful
   ordinary drain return occurs after queue/dirty-work exhaustion and all
   frame-owned acknowledgements. A replay child's cache skip and eventual
   retirement are justified by its persistent two generating bounds, using
   R339, not by memo/stamp membership. R345 supplies the distinct FunctionPort
   and whole-frame retirement cases within its reviewed origin census.

This is not full N, completion of all authentic source inequalities, W/Z/S0,
FreshUse, transport, representative-change coverage, the full language or A/B.
No foreign-continuation/F1/FK1 quantifier is used or discharged.

## A. Exact fibers and the monotone cursor invariant

For a fixed key `k`, a fiber is its attached `RelationId` membership. Its
native witness is a `bound_keys` node `(k,r,next)` reachable from
`bounds[k]`; the node index is the cursor identity. Different keys or relation
IDs remain different incidences, even if their algebraic inequalities agree.
Interning equal child relations does not identify their different Replay
dependencies or operation slots.

`bound_relations`, `bound_cursor` and `bound_entry`
(`candidate_context.rs:3264–3275`) traverse exactly that chain. `attach`
(`3283–3295`) scans the exact key for the same relation and returns without a
write on a hit. Otherwise it uses the fresh vector index, stores the former
head as `next`, and replaces only that key's head. Hence, by induction on
successful attachments:

- each key's chain is finite, contains no repeated node or RelationId, and
  every nonempty link leads to an earlier node of that same key;
- later distinct attachments extend a chain by a prefix; its old suffix and
  links are unchanged;
- a saved nonempty head remains reachable, and a saved `None` denotes the
  empty old suffix/end sentinel.

These are claims for ordinary successful construction, not all mutators in
the file. Test-only removal/restoration at `1991–2023`, route rollback at
`2133–2163`, and canonicalization/transport paths are not ordinary admitted
events here. R336 L0 excludes copied-row intrusion; R337 J and R345's authentic
origin census exclude the other task producers. No test-created state is
used to establish this invariant.

For old published heads `(L0,U0)` and current heads `(L,U)`, define the finite
sequences

```text
NL = walk(L, L0)       OL = walk(L0, None)
NU = walk(U, U0)       OU = walk(U0, None),
```

where `walk(a,b)` includes nodes starting at `a` and stops *before* `b`.
Then `all(L)=NL ++ OL` and `all(U)=NU ++ OU`, with disjoint components in
each sequence. For relation identity these remain disjoint because `attach`
suppresses repeated membership at a key. The generation frontier is a
frontier of attached fibers, not a count of physical bound-vector cells and
not a processing-completion frontier.

## B. The two-region product proof

Let the previously covered product be `OL × OU`. Finite Cartesian-product
distributivity gives

```text
(all(L) × all(U)) \ (OL × OU)
  = (NL × NU) ⊎ (NL × OU) ⊎ (OL × NU)
  = (NL × all(U)) ⊎ (OL × NU).                         (1)
```

Disjointness of the last two regions follows from `NL ∩ OL = ∅` in their
first coordinate; disjointness inside the first region follows from
`NU ∩ OU = ∅`. Conversely, any current pair outside the old product has a
new lower or, with an old lower, a new upper, so belongs to exactly one
region. This proves completeness as well as nonoverlap.

The actual loop descriptors in `candidate_context_begin_replay`
(`candidate_context.rs:4015–4059`) are

```text
(L,  L0,   U, None)      -- NL × all(U)
(L0, None, U, U0)        -- OL × NU.
```

Each outer/inner loop follows exactly one immutable `next` link per
iteration. The source's defensive `None` break does not truncate a valid
nonempty interval: A proved every nonempty stop reachable. The first loop
owns the new/new quadrant, so the second neither duplicates nor omits it.
No attachment, source-action execution or typed dispatch occurs inside
these loops. Relation/context/source-set/scoped interning, recipe publication
and dependency-edge publication do not change these bound chains. Thus the
saved `heads` remain the actual heads throughout this finite generation.

Empty cases are literal intervals: unchanged lower means `NL=∅`; unchanged
upper means `NU=∅`; both unchanged means no visits; an initially unpublished
frontier has `(L0,U0)=(None,None)`, `OL=OU=∅`, so the first region is the
whole current product. If an opposite current chain is empty its product is
empty. The explicit `upper_start==upper_stop` skip agrees with this. Both
frontiers may have grown since their last publication; (1) covers that too.
One actual ordinary bound admission changes only its selected key before
replay, and no frontier changes during the generation scan itself.

## C. Admission-to-frontier induction, including existing physical keys

The base is the fresh ordinary candidate state used by R337: there are no
attached bounds, Replay dependencies or published replay heads. At the
induction boundaries use completed successful owner admissions and their
synchronous generation/queue-transfer calls. Intermediate local ownership is
described below; generation does not wait for child solving.

`candidate_apply_value/effect` selects one row owner/side, inserts the bound,
then calls `candidate_replay_bound` (`candidate_extrusion.rs:1115–1176`).
`candidate_insert_bound_with_evidence` calls its origin/fiber constructor,
appends the addressed direct/exact physical slot, checks full-key readback,
and publishes the emission (`702–875`). Relation attachment therefore may
precede physical append. The pre-append attached key already belongs to B in
R338's interpretation; a successfully returned insertion has both witnesses.

For `OwnerEmission`, `candidate_bound_origin_with_evidence` calls
`candidate_context_bound` **before** the `origin_keys` duplicate branch
(`candidate_effect.rs:530–556`). `candidate_context_bound_for`
(`candidate_context.rs:3888–3937`) interns the bound relation, records Derived
ancestry and calls `attach` for the exact key. Consequently:

- same key and same RelationId leave its head unchanged, even if physical
  storage admits another incidence;
- a distinct relation at a key already physically present is prepended and
  becomes a genuinely new frontier member;
- origin-key duplication alone cannot suppress that preceding attachment.

After successful insertion, `candidate_replay_bound` captures the opposite
physical count and reads every indexed direct/exact entry (`1070–1112`,
`877–938`). The owner and endpoints are fixed representatives. For positive
admission it constructs `(inserted lower, existing upper)`; for negative
admission it constructs `(existing lower, inserted upper)`. Each task is the
same-sort comparison of those bounds' payload endpoints in that order.

The snapshot covers every then-existing opposite physical key: all ordinary
attached fibers were admitted by this same append path, and physical storage
is append-only here. During the scan `begin_replay` only generates metadata/
child storage, and `drive_replay(...,None)` only enqueues; neither dispatches
the new children or appends another bound. Thus the count and indexed contents
remain stable through the scan. A duplicated physical key can cause another
call for the same ordered keys, but its first successful call has already
published the heads and the subsequent unchanged call visits nothing.

Apply B at each selected pair. Previously covered old/old pairs stay covered;
all new pairs receive the exact generation witnesses of D. Every affected
opposite key has been selected when this admission returns. If the opposite
lane was empty, there was no product yet; its later first insertion scans
the now-existing current-side physical key. This induction establishes
temporal coverage of the attached fiber product for every fixed ordered key
pair actually formed by this ordinary path. It does not assert that every
source-required constraint necessarily reaches this path.

## D. Exact dependency keys and publication ownership

For each visit, `begin_replay` constructs the child from the unchanged task
pair, actual lower/upper contexts, unioned source sets and composed scoped
flow. R337 supplies identity contexts/default flow without erasing ordered
ancestry. `Dependency::Replay` derives exact equality/hash on

```text
(child, lower_relation, upper_relation, lower_input, upper_input).
```

It retains both ordered parents and both exact keys
(`candidate_context.rs:331–355,4036–4057`). Equal child IDs from different
parent pairs still create different dependencies and separate `children`
slots. Set-idempotence of their task formula does not merge those slots.

`evidence.recipe(dependency)` precedes the dependency-key check. A recipe is
not a work item or completion certificate; its explicit coverage marker is
`ReplayUseAntecedentsNotRetained` (`889–900`). The relevant publication is
`dependency()` and then `replay.push(child)`. The vector capacity has already
been reserved, so that push is infallible after dependency success.

There is only one production construction of this Replay variant: the visit
just described. Other `Dependency::Replay` occurrences in this pinned module
are matches/readers. Tests, incoming-use replay and failed/rolled-back private
routes do not supply earlier keys in this authentic ordinary history. This
gives a useful stronger induction invariant: every retained exact Replay key
has a particular earlier successful generation event and child slot, or is
currently being published into the generation local before that constructor
returns.

In fact a newly visited delta pair cannot already have its exact key. If its
key existed from an earlier completed generation, that generation visited the
same ordered parent memberships at the same input keys. Its published heads
therefore included both memberships. Every subsequent publication only
extends those prefixes, so both would be in today's old suffixes. That
contradicts membership in (1). Within one call, B visits each ordered parent
pair once, so an earlier iteration cannot create that exact key either.
Dependency equality includes the parent IDs even if the child is interned.
The recipe table does not change this argument because it is a different map.

The code nevertheless correctly treats an exact preexisting key as a skip.
To count a **prior** dependency as prior coverage, the source-history invariant
locates its earlier batch O and slot j. Before acknowledgement, O retains
`operation.task` for j even when its queued copy has left the worklist; the
item is in Q, a dequeue local, or the actual frame/current/ack ownership chain
of E. After acknowledgement, E supplies the exact dispatched-and-terminal
processing history; operation reclamation is possible only after the last
slot is consumed. A bare key in a fabricated entry state establishes none
of this. This is operational history derived from actual constructors and
consumers, not a new H conjunct or an inference from a completion stamp.

After every loop visit, all newly admitted dependencies have child slots in
the live Rust `replay` vector. Only then may `replay_progress` publish heads
(`3276–3281,4060–4073`). The actual order is progress, checked child-byte
accounting, then `ReplayOperation` insertion by `mem::take`. During that
interval the vector/local task owns the generated work; no solver dispatch
or attachment can observe an advanced frontier while creating a competing
generation. At successful return all slots have moved to O with frozen task,
inputs, heads and prior, and zero queued/consumed frontiers. This proves that
a successful publication does not advance past unrecorded generated work.
It does **not** assert atomic publication on an intervening allocation/
arithmetic/resource error, safe reuse of an abandoned private state, or that
the operation already exists at the earlier progress statement. Those would
need a separate failure/retry owner proof. Successful intermediate states
retain the local owner; they are not falsely represented as durable O slots.

## E. Actual queue, typed drain and acknowledgement ownership

Use the production `None` adapter, not the test publish-closure harness or
the restoration adapter that launches a synchronous child drain.

1. `ReplayOperation` stores its exact task and child vector
   (`candidate_context.rs:126–143`). For each `j=queued`,
   `replay_operation_queue_next` returns exactly
   `{task:O.task, relation:O.children[j], ack:(O,j)}` (`2369–2375`).
2. `candidate_context_consume_replay_child(...,None)` calls `enqueue_item`
   for that item (`4185–4200`). Queue/evidence/undo preflight precedes
   `transfer_replay_child`; only infallible deque insertion follows
   (`lib.rs:15223–15250`). Transfer checks exact operation/index and Idle/
   nonretired status, advancing `queued` once (`candidate_context.rs:
   2384–2396`). O still retains every unconsumed slot.
3. When all slots are queued but some unconsumed, consume returns false
   without acknowledging them. `drive_replay` returns `Queued`, explicitly
   leaving completion to the outer worklist consumer (`4207–4228`). A batch
   with no children can be retired immediately; it owes no typed work.
   For a nonempty batch no Queued return is a drain-completion claim.
4. The actual ordinary source drain was created by `start_typed_drain`
   and driven by `run_candidate_typed_drain` (`lib.rs:14186–14270`).
   Transport reserves ack ownership, pops the exact item, stores current and
   retains its ack in `frame.replay_acks` (`14301–14333`; dequeue
   `15166–15173`). The local owns it between deque and frame publication.
   O still owns its unconsumed slot, so this intermediate transfer loses
   neither task nor completion responsibility.
5. Transport preserves the task/relation under fixed representatives;
   Context returns false under J. Dispatch copies the exact current item
   with the ack cleared only in that dispatch local: the frame already owns
   the ack. It processes the task or takes its supported cache skip, and
   clears current only after immediate dispatch or completed structural
   child transfer (`14335–14376`). Thus a frame ack cannot arise merely from
   generation or queue insertion.
6. All slots of O were queued at the back in increasing j before ordinary
   replay returned. Later front insertions of Function children do not
   reverse those existing queue items; back insertions of further batches
   also preserve their relative order. Pops therefore encounter O's acks in
   increasing j. Terminal consumption additionally checks exact
   `operation.consumed==ack.index` (`candidate_context.rs:2444–2452`), so a
   successful terminal path cannot silently acknowledge another slot.
7. Acknowledgements occur only after Diagnostics. Terminal code calls
   `complete_replay_child` for the owned ack before incrementing the frame
   counter (`lib.rs:14923–14933`). `acknowledge_replay` advances consumed,
   retires only at `consumed==children.len()`, and reclamation removes only
   a retired ordinary operation (`candidate_context.rs:2190–2203,
   2397–2403`). Consequently an earlier removed O supplies actual terminal
   processing history for every slot, rather than only an inert key.

This proves the ownership disjunction used in D by induction on actual
transfer/dequeue/dispatch/terminal steps. While an ack is pending, R retains
the child even after dispatch has cleared current. After consumption,
logical retirement needs the separate support in F; ownership alone is not
an entailment proof.

## F. Cache suppression and logical support

Let q be any child enumerated by B. Its actual selected bound keys have a
common row owner o, positive lower payload l and negative upper payload u.
The successful admission/selection path in C supplies persistent physical
incidences `l ≤ o` and `o ≤ u`. For every assignment on the fixed row set,

```text
ρ ⊨ B(S)  ⇒  ρ ⊨ (l ≤ o) ∧ (o ≤ u)  ⇒  ρ ⊨ φ(q).       (2)
```

The last step is R336 Value-preorder or Effect-subset transitivity. It does
not use concrete optional-record transitivity. R339's independently accepted
ordinary replay theorem supplies persistence of these exact physical bounds
through cache, ack, reclamation and containing frame retirement. It applies
to each actual q here because C established its precise producer/antecedents,
not because its relation has a familiar shape. Arbitrary symbolic latent
Effect sets remain quantified; no empty-effect valuation is imposed.

`pair_is_current` checks a typed memo plus the processing relation's generation
stamp (`lib.rs:13507–13518`). `mark_candidate_pair` writes the stamp before
apply/decomposition completes (`candidate_intrusion.rs:423–455`). Neither
the bit nor the memo is used as proof of prior completion. If this q is
cache-suppressed at `dispatch_live_item` (`lib.rs:14439–14463`), (2) supplies
its exact independent logical support. E establishes that its actual cache
check was reached through the typed consumer and its ack remains owned; the
skip need not emit another owner fiber or replay its structural children to
retain q as an algebraic consequence. This distinction prevents upgrading
the present result to every possible downstream/source interaction.

At acknowledgement and final pop, (2) also justifies removing q's last work
copy. For a non-hit Function q, R345's reviewed four-port argument and actual
FunctionAdmission/Enqueue sequence cover the distinct descendants; those
ports are supported by authentic Function ancestry, not assigned q's direct
two-bound witness. R345 also supplies the independent initial/current,
designated/processing and saved-processing restoration retirement premises.
Applying these results to this newly established generation trace supplies
bounded N/D2 support across the entire named ordinary drain family, without
claiming that generation coverage alone proves all N transitions.

## G. Reachable ordinary return and application to N

In `step_typed_drain`, Transport with no current first settles intrusion when
the typed worklist is empty, then attempts a pop. It enters Diagnostics only
when the pop is None and `dirty=false` (`lib.rs:14289–14333`). Under L0 there
are no pending copied-row intrusion parents; `settle_candidate_intrusion`
clears dirty in its empty-pending branch (`candidate_intrusion.rs:568–581`).
Thus empty queue alone does not bypass outstanding dirty work. The general
merge loop is not imported as a fixed-representative theorem.

An active Function dispatch cannot reach this no-current Transport state
until all its actual children have enqueued; R345's reviewed construction/
terminal inventory establishes that fact. Diagnostics creates diagnostic
evidence, not new typed work in this K0 family. Only after it finishes does
the driver enter Acknowledgements (`lib.rs:14403–14418`). Terminal validation
requires the top frame and valid ack-frontier inequalities; ReturnReady
additionally requires `completed_acks==replay_acks.len()`
(`14881–14945`). Its successful pop restores the exact saved processing pair
and relation, with the distinct identities handled by R345. These facts
derive reachability from the actual driver; a hand-built ReturnReady frame
would not suffice.

Accordingly, **if** this ordinary drain returns, every generated item that
entered it has traversed its actual consumer/cache branch and every ack it
owns has been consumed; no live typed queue or unsettled K0 dirty work was
bypassed. E explains the exact generated slots, and F explains their logical
support even on cache skips. This is finite-prefix partial correctness,
not an assertion that a queue will eventually drain or all inference ends.

Apply the lemmas to `R345-N-REMAINDER`: previously R338/R339/R345 only
established consequences/retirement for work that was already generated.
A–D now establish complete temporal emission of the attached-fiber product
for the fixed ordinary OwnerEmission pair family. E–G connect those emitted
slots to the actual completion boundary, supplying this particular I-work
premise to N/D2. The two-bound interpretation remains independently supplied
by F. This is a genuine reduction of the parent remainder, pending review,
with no claim that H equals the TeX typed semantics.

## Remaining premises, falsifiers and mutual TODOs

`R346-REVIEW` — Luna owns fresh non-contributor review of this frozen proof,
the primary census and the pins below. Challenge the no-hit strengthening,
authentic constructor census, pre-append/progress local ownership, exact
parent and slot identities, ack ordering, cache witness and terminal
reachability. This producer and the complementary census author cannot
independently certify the combined result.

`R346-N-REMAINDER` — Luna retains full N/cache/source-constraint completeness.
First missing evidence outside this supplied family is a complete authentic
source-constraint-to-live-or-entailed end-state inventory across all required
origins and consumers, including source cache suppression before any
OwnerEmission and interactions outside fixed-key ordinary replay. Inputs are
accepted R336/R337/R339/R345 plus this result only after its independent
review. Proposed output is the exact remaining owner-specific correspondence
or a source-qualified missing necessary interaction. Falsifier: an authentic
successful source constraint or required relation interaction absent from
all actual live/completed consumers **and** without the algebraic support
needed by its claimed N instance. Merely absent scheduling is a coverage
gap; it is not automatically a semantic counterexample.

The first source owners to retain are `candidate_bound_origin_with_evidence`,
`candidate_context_bound_for`, `candidate_replay_bound`,
`candidate_context_begin_replay`, `dispatch_live_item` and
`candidate_step_typed_drain_terminal`. FreshUse/restoration,
BoundTransport/canonicalization, new rows, whole-solver Z, W, G completeness,
S0/C/M, boundary/effect semantics, principality and original A/B remain OPEN
with their existing owners and independent quantifiers.

`R346-IMPLEMENTATION` — `NO_SAFE_CODE_SLICE`. The pinned insertion/replay
and typed-dispatch/terminal owners were inspected; no actual source-qualified
compiler defect or provisional instrument is established. If review finds a
reachable owner mismatch, Luna must allocate the minimal owner-local readback
or repair. Its exact falsifier must exhibit the first authentic admission/
generation/queue/terminal event violating one of A–G, and separately test
whether a valuation/source observation witnesses a semantic failure. This
TODO grants no code lease, dependency expansion or production authority.

In-envelope falsifiers are: a distinct ordinary fiber linked behind a saved
cursor; a relevant head mutated during one generation scan; an attached
ordinary key without its successful physical append when the admission
returns; a visited exact-key hit lacking the earlier slot history; progress
passing a generated dependency without its local/operation child; a lost or
reordered ack accepted as another index; successful ordinary return with a
generated queue/dirty obligation remaining; or a claimed cache-retirement
instance without its exact R339/R345/algebraic witness. A fabricated frame,
assumed-transition test, non-K0 source, or failed private state cannot serve
as a source-qualified falsifier to this fixed claim.

Reused: R336 rev4 algebra/L0, R337 J and authentic prefix, R338 independent H
and owner orientation, reviewed R339 replay witness and reviewed R345
retirement/Function origin census. Rejected: memo/completion/recipe labels as
proof, old conditional restoration results beyond their premises, physical
duplicate counts as distinct fibers, and equality of task formulas as
lineage identity. No theorem is rescued by reducing ordinary inference.

## Frozen pins, provenance and execution receipt

R346 revision-1 governing contract SHA-256:
`7f2419fa4d589ec6bb7d8af769a3eeb94f5361332483321328a06c2558327391`.
The first compact snapshot contained the stale `252a7247…` contract pin;
Luna acknowledged trailing-whitespace cleanup and reconciled the exact
`7f2419fa…` pin before this artifact was written. Scope/revision are unchanged.
Baseline `research/simple-sub-intrusion` /
`a5edc8ee72b7fb1062b8d83d0753b1d43ec76702` is contract metadata; this worker
performed no Git observation.

| Direct dependency | SHA-256 |
| --- | --- |
| Original user audit, `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| `docs/yulang-whole-language-semantics-ja.tex` | `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612` |
| Aligned user crosswalk | `bea755595302d5b98fb1880fb89b505ad783a6e428c639aae6734b167df86d65` |
| R345-aligned user revision | `ba0c2badb5fa4abd5f3102cd8ce21dcdf33f4441c7f92204023379bb8ccc9a07` |
| `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md` | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| `notes/theory/2026-10-23-r337-k0-context-preservation.md` | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| `notes/theory/2026-10-23-r338-k0-d1-d2-state-bridge.md` | `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0` |
| `notes/theory/2026-10-23-r338-k0-state-source-census.md` | `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9` |
| R339 sequential rev2 contract | `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00` |
| `notes/theory/2026-10-23-r339-k0-obligation-retirement.md` | `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87` |
| R339 outcome/review | `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701` |
| `notes/theory/2026-10-23-r345-k0-initial-drain-preservation.md` | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` |
| `notes/theory/2026-10-23-r345-k0-initial-drain-source-census.md` | `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b` |
| R345 outcome/review | `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce` |
| Primary R346 source census | `1179312d8230616a0ac5cda45a1c29f08012bba9327f2f3601bb3179cfb5fdfd` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

Historical authors (inherited provenance): R336/R338 primary `/root` and
`/root/r336_k0_algebra_prover`; R337 `/root/r337_k0_context_prover`;
R339 `/root/r339_obligation_prover`; R345
`/root/r345_k0_initial_drain_prover`; source censuses `/root`. User document
individual authors are UNKNOWN. These contributors do not certify R346.

Checks: read-only source inspection, manual induction/product/algebraic
reasoning and direct SHA-256 comparisons. No tests, builds, Cargo, execution
probes, production edits, Git, network/external contact or descendants. Only
this artifact and `tasks/agent-loop/inbox/20261023-r346-k0-replay-prover.md`
are new paths; no scratch paths. Requested role/model/effort:
prover / `gpt-6.1-sol` / high. Effective observed model/effort: UNKNOWN/UNKNOWN.
Actual worker identity: `/root/r346_k0_replay_prover`; parent records session
`01a165ee-0212-7af3-8c99-1c1efcf367fe` and launch at 09:31:30 UTC.
Worker-local first clock: 2026-10-23 09:35:06 UTC. Full 3000-second grant is
charged conservatively; no renewal/carryover. The exact final clock, artifact
hash and writes-stopped receipt are in the assignment handoff. This producer
stops writing at submission; no worker or descendant remains computing while
review waits. Luna owns independent review, adjudication and integration.
