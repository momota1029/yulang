# R48 actual-route temporal transport: owner-derived replay contract

Status: frozen candidate conditional mathematics and static source/native audit;
not an independently reviewed theorem or actual execution receipt.
Assignment: `R48-SOL-TEMPORAL-PROOF`, revision 1.
Derivation author: `/root/r48_temporal_transport_proof`; implementation-design
input: `/root` (Luna). No descendants. Both are producers of the combined component.
Contract: `actual-route-temporal-transport-20261019-r48`, revision 1,
SHA-256 `e17bd3f602cb00cb600d6647432a18cc6df5d5ce8d5eb59a78eba52eb8dfbc5a`.
Baseline: parent-supplied `ec1ba3ce2fa9553c821ac0ecb708adc9107ce136`;
no Git operation performed.

## Result and application to the original parent

A complete owner-authenticated ordered test-only history is sufficient to
authenticate the bounded inspection edge, including intervals with no forest
change and intervals containing rollback. The proof is a finite replay
induction over the actual forest mutations below. Completeness is a separate
source-coverage premise, not a property inferred from a log, a generation
counter, or a successful test. At the pinned baseline that premise is absent:
`MISSING_RETAINED_EVIDENCE` remains at capture/reconstruction, forest mutation,
rollback and the inspecting join. No actual q transport success is claimed.

This replaces the unsupported equality of historical source S with current
representative by a time-indexed relation preserving raw S and tracking its
later representative. It retains R47's reviewed constructor-specific no-hit
result: both actual helper preparations start with distinct captured roots and
an empty canonical map, so every recorded row is a miss. A no-change interval
is legitimate evidence when authenticated as complete; no hit is required.

Applied immediately to the original full inference/evaluator parent, the result
identifies an implementable bounded native transport prerequisite and its exact
remaining source evidence. The original theorem and Simple-sub A/B remain
**OPEN, 0 -> 0**. Recursive worlds, arbitrary W, both frames, aliases, complete
Call/effects, independent effect/result origins, F1 and FK1 as distinct
quantifiers, N-Transport, soundness, principality and termination are preserved.
No `Desc`, exact ordered `D_q`, complete Call rule, evaluator theorem, source
admission change or production authority follows from this packet. One local
route action does not discharge foreign-continuation quantification.

## Minimal relation and what “complete” means

Use cuts in one ordered owner history, not wall-clock time or solver generation.
For one session let `F_t^V,F_t^E` be the two partial parent arrays at cut t.
`R_t(k)` follows the array of k's kind, returning k if its ordinal is outside
the array, exactly as `representative` does. Existence in live row storage is
a separate predicate: an implicit identity forest entry is not allocation
evidence. Let `A_t` identify the live allocation lifetime of each tracked key,
and `Q_t` identify retained local frames/completed routes and their owners.
These auxiliary observations describe existing operations; they add no solver
transition or source semantics.

A history sufficient for the bounded query contains:

1. An authenticated initial forest snapshot (or a complete prefix from empty
   initialization), including array lengths. Absence outside an array is part
   of the snapshot. Sampling only selected final representatives is insufficient.
2. An ordered event for every actual array mutation after that snapshot:
   identity extension, union assignment, compression assignment, reverse undo
   assignment and truncation. Each event records kind, owner, old/new contents
   or lengths, and a position. Events are appended at the actual mutation,
   including a write followed by a fallible error before generation increments.
3. Capture and reconstruction cuts tied to their actual owner records, immutable
   raw requested/captured/source/image keys, graph row and route/frame identity.
   A record supplied by a caller is checked against the retained owner record.
4. Retained-route/allocation survival evidence adequate for every tracked key
   and route, established by transaction markers or the structural owner
   argument below. Explicit begin/commit log markers and a global birth-ID
   system are not required. If a
   numeric ordinal can be truncated and reused, its lifetime must be distinguished
   or reuse ruled out on the accepted interval. A final ordinal alone cannot do so.
5. An inspection cut closing the interval. The observation history survives
   rollback; successful commit does not erase it. The validator rejects a gap,
   unsupported event, unsupported survival claim or stale lifetime.

This is sufficient information, not a requirement to allocate a new full forest
snapshot per row or log unrelated semantic state. A single shared snapshot and
history can serve all rows and routes; indexed positions select the relevant
intervals. A smaller representation is valid if it establishes the same
equalities, absence and lifetime facts at the actual owners.

Completeness is established by exhaustive audit of writes to the private arrays
and route/lifetime owners, plus trusted owner placement of cuts. No event may
be silently dropped on a bounded-log overflow and still permit acceptance;
reject the observation instead. Replay of an assumed event stream alone is
conditional mathematics, not evidence that these source owners emitted it.

## Derivation from the pinned owners

| Actual owner | Transition and obligation for retained evidence |
| --- | --- |
| `candidate_intrusion::representative`, `State::rep` | Read-only traversal; separate value/effect namespaces; out-of-array key returns itself. No compression is hidden in `rep`. |
| `retain_extrusion_parent` | Extends each forest with identity entries up to current live bounds lengths, then retains the actual signed Parent. Extension changes representation but no existing representative. Record its range, or prove an equivalent complete prefix/implicit-identity rule. |
| `merge_candidate_rows` | Canonicalizes actual copy/parent first. Equal roots return with no write. Unequal same-kind roots transfer both bound sides/origins, combine level by min and non-generic by OR, then assign copy-root to parent-root. Record the actual assignment, not merely successful function return. |
| `compress_candidate_forests` | For each rewritten link, stores old link in active Undo and assigns the current root. Preserves representatives but changes array contents; source coverage must include these writes. |
| `State::begin` | Checkpoints forest lengths, generation, provenance lengths and pending state; starts an empty list of old forest links. A checkpoint is not forward-history evidence by itself. |
| `State::rollback` | Restores `Undo.forests` in reverse, truncates identity-extension suffixes, removes born provenance/groups, and restores generation. Retain rollback outcome and these actual writes/truncations outside the consumed Undo. |
| `lib::finish_route_transaction_with_candidate_accounting` | Success releases `journal.intrusion`, commits context replay operations and transfers a completed Local via `GraphState::commit_local_use`. A paused successful frame can remain retained before its later completion. |
| `lib::rollback_route_transaction` | Calls intrusion rollback, restores retained cursor or clears newly created local frames, removes born local-route occurrence entries, truncates routes, and restores allocations. Existing routes survive; a route born in an aborted transaction cannot authenticate a later query. |
| `Capture::row` | Samples `requested=K`, `C=R_c(K)`, deduplicates by C, and retains only first-insertion row observation. A dedup request is not an independently retained occurrence. |
| `prepare_candidate_fresh_use` | Samples `S=R_r(C)` and selects raw image I with the existing local/level/non-generic guard and per-preparation map. Preserve S; do not overwrite it with `R_f(C)`. |
| `GraphState::commit_local_use` | Moves the actual graph/rows/maps and exact local occurrence/use instance into one retained route. Authenticate this transfer and route survival, not endpoint shape. |
| `captured_source_matches`, `join_apply_pair_capture` | Must consume authenticated historical cuts and replayed inspection identities. Baseline comparisons of raw historical S with current `rep` do not supply that evidence. |

The mutation audit finds the private forests initialized at empty State,
extended in `retain_extrusion_parent`, assigned in union/compression, restored
and truncated in `State::rollback`. These owners are the finite coverage seam.
The separate live allocation owners are `fresh_value_at_level` and
`fresh_effect_at_level` in `lib.rs`; route rollback truncates live storage.
The permitted test-only overlay need not edit those functions if its retained
transaction lengths and route/image allocation owners already prove survival.
If they do not, this is an exact missing premise requiring Luna's lease decision,
not permission for this leaf to add another hook.

### Replay induction

Assume the initial snapshot equals the actual arrays and every event is emitted
at its actual owner without omission. Induct on event position. Identity
extension appends the same self-links as source. Union and compression replace
exactly the recorded link, after checking the old link against the replay
state. Reverse undo restores exactly its recorded prior value; truncation
removes exactly the suffix removed by source. Read-only cuts and commit outcomes
leave the arrays unchanged. Thus the replay arrays equal actual arrays at every
cut. Deterministic traversal gives replayed `R_t(k)=actual R_t(k)`.

The forest remains acyclic on successful existing operations: initialization
creates self-roots, union connects unequal roots of one kind, compression points
to an existing root, and reverse undo/truncation restore an earlier forest.
This argument does not require union to have completed replay or incremented
generation: a partial union write is still an event and its later undo is still
replayed. The existing journal may contain a saved link for an assignment never
reached; restoring that same value is a legitimate no-op.

If no forest mutations occur between two authenticated cuts, replay states at
those cuts are equal. This proves interval stability, including a fully logged
empty interval. Endpoint equality or equal generation without completeness
cannot prove this negative statement. A union followed by rollback can return
both representative and generation to their previous values.

Route/allocation validation is separate from forest replay. An aborted capture
or reconstruction remains a historical event, but cannot be used as a surviving
route map. A reused raw ordinal belongs to its new lifetime. The replay proof
never turns it into the old object. Rollback may split a class formed during
the aborted attempt; do not assume a global monotonically growing equivalence
relation across rollback. Recompute at every requested cut.

### Why surviving route ownership can replace explicit transaction markers

The pinned source supplies a smaller lifetime proof for this consumer. At
transaction begin, `journal.candidate_local_use` records the cursor of an
already retained frame, if any; the live row lengths are checkpointed. On
rollback a newly created frame is cleared, whereas a frame already present
has its cursor restored. Completed new routes and their occurrence-index
entries are removed by route truncation. On success only the completed actual
frame is moved into `local_routes`; its graph/maps are not reconstructed from
caller-supplied data. A successful pause can retain the same frame for later
transactions before its final completion.

Inductively, every frame/route currently retained was created in a successful
transaction or existed before the current checkpoint. Its captured keys and
fresh image allocations were live when its owner records were created. After
the creating transaction succeeds, every later checkpoint's live-row lengths
include them; later rollback cannot truncate/reuse those ordinals while leaving
that frame/route retained. The same argument covers graph keys whose forest
entries are implicit identities: existence of the captured root comes from
capture's successful live level/metadata lookup, not `rep` alone. A requested
key either lies inside the valid forest prefix or is its own implicit root;
in the latter case its equality to that validated captured root proves its
existence. Forest initialization and checkpoint restoration keep forest
prefixes/links inside live row storage. Reconstruction source S is a root
of those live forest links; fresh I is an actual successful append at the
owner, or the recorded no-allocation source. Thus authentic membership in the
current `local_routes`, together with owner-bound capture/reconstruction maps,
can establish the needed lifetime without instrumenting `lib.rs`.

This argument uses the actual rollback/commit implementation as a static
dependency; it does not infer survival from a final representative or test.
It requires a single exact frame/map lineage moved by those owners and the
existing transaction length invariants. A copied supplied map, synthetic route,
record from an aborted newly created frame, or undocumented frame replacement
does not satisfy it. An implementation changing those ownership operations
must reestablish the argument. No general rollback correctness obligation is
added to the inference theorem.

Accordingly Luna's proposed design—one capture-time full forest snapshot plus
cursor, monotone actual forest-write/restore/truncation log outside Undo,
reconstruction cursors and fresh-image owner facts, and replay compared with
the full current forests—has sufficient information **conditionally on** the
write-coverage, failure and owner-lineage obligations above. Explicit
begin/commit events are unnecessary for that design. Final full-forest equality
is an additional replay consistency check, not proof that an omitted write and
later inverse write never happened. Source coverage still establishes absence.
This assesses the design described by Luna, not a moving implementation diff.

## Signed C/D and the two actual helper routes

For each accepted route h and each coordinate s in
`{C = argument/Positive, D = result/Negative}`, authenticate this tuple:

```text
(session, exact q checking occurrence/event, group/occurrence,
 indexed signed Parent p, h's local/use occurrence/use instance,
 graph row i, capture cut c, reconstruction cut r, inspection cut f,
 requested K, capture C_i, raw source S_i, raw image I_i, lifetimes)
```

The existing indexed Parent/group/source-event/structural-comparison checks
remain required. Pair polarity and expected raw parent are checked separately;
current equivalence cannot substitute one coordinate for the other. The exact
q is the nested `loop y` Apply, distinguished from direct `loop x` by source
occurrence, its Candidate recipe, schedule and checking event. Neither a test
declaration nor the existence of those static objects proves execution reached q.

At capture require replayed `R_c(K)=C_i` and the selected signed endpoint's
capture-time representative to equal C_i. This can authenticate a canonicalized
request even when the original raw signed endpoint differs from K. It does not
invent a separate dedup request record. At reconstruction require `S_i=R_r(C_i)`
and the exact owner-selected image I_i. At inspection replay each relevant raw
key separately; check the endpoint-to-capture/source equality needed by the
consumer using `R_f`, and inspect the raw image through its own valid lifetime.
In particular, `R_f(S_i)` may differ from raw S_i. No general equality between
image and source is asserted: a fresh image is a reconstruction mapping, not
an intrusion union. Preserve parent and copy lineages even if later equivalent.

The selection must be tied to the capture-time signed endpoint, not merely
`.position` in a final canonical class. A late merge of a previously unrelated
row must not fabricate historical pair membership. If the bounded consumer
chooses a current-class member, it must separately prove that member's capture
edge for this signed endpoint or reject it. This is an evidence requirement;
it does not restrict ordinary inference or prohibit later legal merges.

The same validation runs independently for h0/C, h0/D, h1/C and h1/D, including
the selected parent-side row as well as copy-side row. h0 and h1 have distinct
source-use occurrences and retained maps. Current representative equality does
not collapse their route identities. Their images need not be unequal. Equal
graph row indexes across routes, if observed, prove no cross-route ownership.

R47 applies separately to each h: capture and reconstruction are immediate,
capture deduplicates while the forest is fixed, preparation/row allocation do
not merge existing classes, and each preparation map starts empty. Therefore
all rows have hit=false, first-entry=self, existing-image=None. The guard either
allocates a fresh same-kind image or reuses raw S. Later restoration/link solving
can merge representatives but cannot change those recorded choices. R48 accepts
this actual no-hit route; it does not revive R47's unreachable later-hit demand.

## Falsifiers, remaining evidence and mutual TODOs

`R48-TODO-OWNER-LOG` to Luna's test-only implementation lane: supply the finite
mutation/rollback coverage and authenticated cuts above. Inputs are the pinned
owners. Proposed outputs are only the already leased candidate source overlay
and implementation receipt. Falsifier: one actual array write omitted from the
history, a partial-error write logged only on success, an unlogged rollback
restore/truncation, a gap silently accepted, or a stale lifetime accepted after
ordinal reuse. A fabricated stream that replays consistently is not source
coverage evidence. Parent application remains bounded native transport only.

`R48-TODO-Q-INSPECTION` to Luna: establish actual q/event/group, both signed
coordinates, both retained helper routes and their surviving allocation/route
owners at the final inspection. First consumer owners are
`captured_source_matches` / `join_apply_pair_capture` and the existing
`active_outer_root_two_helper_uses` fixture. Falsifier: wrong q, wrong structural
comparison, forged indexed Parent, wrong polarity/coordinate, sibling map, stale
route, final-class-only selection, or absent transition accepted. Preserve all
existing negative substitutions. Only the contract's post-review focused test
may provide execution evidence; this worker runs none.

`R48-TODO-REVIEW` to Luna: freeze the implementation/proof component together
and assign fresh isolated review. This producer/coauthor is ineligible to
certify that component. A review of this baseline derivation cannot certify a
later moving overlay. If the exact q route or lifetime evidence needs an
unleased source owner or production invariant, stop at that missing premise.

The bounded claim is now a precise conditional replay lemma plus an exhaustive
baseline mutation-owner audit. The remaining premise is actual retained owner
evidence and q inspection, owned by the assigned implementation lane. It is
not another renamed parent theorem and does not close the parent.

## Frozen dependencies, checks and resource receipt

All ten direct dependencies and the R48 contract matched at intake. Their
recheck is recorded in the assignment inbox; the two implementation source
files may subsequently change only under Luna's already granted overlay lease.
This derivation is about the pinned baseline bytes below, not an implicit
certification of that overlay. Existing source authors are UNKNOWN; prior
proof author is `/root/r47_temporal_copy_proof`; R47 independent reviewers are
`/root/r46_compiler_review` and `/root/r46_spec_review`.

| Direct dependency | SHA-256 |
| --- | --- |
| R47 contract | `aba8009c8ec658af48ed2844e6a9c9b4554b4343ada19f8a7aae85b978574131` |
| R47 proof | `2a8a076a2d245baf367a377a167de7ec6c1c499693934fb17610f69554c37d26` |
| R47 compiler review | `fd2e19217fcfa5394a84471b86aad0c4d55e163634439e6f6f48ba443fcd1460` |
| R47 spec review | `2fa089b56d5f201e5e182cbc15cafab0508aac5d8fa00fb0d671f0942c867f46` |
| `candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` |
| `candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |

Prior work reused only within premises: R47's independently reviewed immediate
helper no-hit induction and missing-history audit. Rejected: final `rep` as
history, generation-only stability, existential hits from conditional branches,
first-final-class selection as historical pair membership, and source formation
or foreign-continuation closure from this native lemma. Historical R37/R46
claims are not reopened or silently promoted.

Checks: read-only `cat`/`sed`/`rg` owner/authority inspection and SHA-256 checks.
No executable simulation, runtime probe, test, Cargo/build, compiler/source edit,
Git, external contact, scratch path or descendant. The only new paths are this
artifact and `tasks/agent-loop/inbox/20261019-r48-proof.md`.
Requested model/effort: configured Sol/high (launch request recorded as
prover/high). Observed model/effort: UNKNOWN/UNKNOWN; no runtime metadata
established either. Grant: 900 seconds, fully charged on issuance; no refund or
budget expansion. CPU/RSS and exact grant-start time UNKNOWN. Clock/resource
recheck is in the inbox.

Stop condition: exact missing actual retained evidence at the permitted
implementation seam. Next step belongs to Luna: consume these obligations in
the test-only owner ledger, freeze jointly for independent review, and exercise
only after its gate. This packet is pending review/integration and does not
claim continued work while waiting. **WRITES_STOPPED; NO_DESCENDANTS** after
the one assignment inbox is frozen.
