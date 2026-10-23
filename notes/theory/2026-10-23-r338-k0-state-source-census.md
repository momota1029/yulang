# R338 — K0 D1 composition and D2 state/source census

Status: primary-adjudicated revision 2, frozen for narrow delta review. D1
composition and the post-admission owner-record/enqueue lemma passed review of
revision 1; this source-admission correction has not had delta review. This is
a source-reading result only, not a machine-checked proof or compiler change.

## Authority and inputs

The governing user audit is
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
The fixed compiler baseline is
`17e57af2c4605d7084c7d76792b115674776bbe2`; all eleven R337 production-owner
hashes below match that baseline and the inherited R337 manifest. R336 rev4,
R337 contract/proof/census and review inputs match the R338 contract pins.

| Production source owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

## D1 composition seam

R336 rev4's conditional constructor theorem has the exact shape

```text
ValidK0(s) ∧ CompleteK0Construction(s,C_s)
∧ ρ ⊨ H(C_s) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ e_s : ρ(v_root) ! ρ(ε_body).
```

R337's reviewed lifecycle result quantifies over finite reachable successful
prefixes of the same authentic ordinary `ValidK0` source and supplies default
`ScopedFlow`, no reachable Allowance, identity relation/post-check contexts,
and their preservation across the listed constructors and drivers. Its input
domain and endpoints match R336; it adds no source restriction and does not
replace `CompleteK0Construction`, `ρ ⊨ H(C_s)`, or `Reifiable₀(ρ)`. R336's
root-output Value Link and Value-subsumption step remain necessary, and the
conclusion continues to report the body evaluation Effect endpoint (there is
no root Effect row).

The composition is therefore conditional on one assignment satisfying the
authentic complete K0 source constraints, with the R337 lifecycle invariant
holding along that same successful construction. The context result makes no
claim that such an assignment exists or that propagation retained every
constraint. This is the exact seam for independent review; until it accepts
the conjunction, whole D1 remains open.

## State interpretation for the bounded D2 family

For a fixed row set and active driver continuations, use the proof artifact's
`H(S)` interpretation: a set of directed Value/Effect inequalities consisting
of:

1. the logical inequalities represented by canonical owner bounds in the
   Value and Effect bound vectors, including retained owner-side keys with
   attached relations;
2. every pending typed-worklist item;
3. every active initial/current request, pending dispatch item, designated or
   saved processing pair, and admitted source/work task in a caller/local
   transfer slot before publication;
4. every uncompleted child obligation retained in a live `ReplayOperation`,
   whether or not it has transferred to the typed worklist yet; and
5. explicit remaining child tasks in any unchanged suspended structural
   dispatch frame.

`Sol(H(S))` is the set of assignments to these fixed K0 rows and endpoints that
satisfy every inequality in the independent K0 Value preorder or Effect
subset order. `H(S)` is a set, not a count of physical vector cells: duplicate
facts, bound incidences, queue items, or relation evidence denote one logical
inequality. A physical slot or evidence record is not itself the definition
of a logical constraint.

`ConstraintStore` membership and provenance identify authentic source
admission; they do not add a second copy of an inequality to this `H(S)`.
After either an accepted or duplicate receipt, `admit_collected_fact` publishes
the incoming task `q` into a caller/local transfer slot and then active typed
work until its identical owner bound is recorded. The store delta differs
(fresh `FactKey` versus existing `FactId`), but both success branches enqueue
the task. Thus source ingress is modeled as

```text
H_after_admission = H_before_admission ∪ {q}.
```

Its solution set may shrink. Equality with the prior solution set follows only
if `H_before_admission` already entails `q`; duplicate `FactId` identity alone
does not establish that premise. Existing entry bounds/work must project to
their indicated inequalities. This local premise is not a claim that completed
native state captures every source fact.

The distinct administrative step begins only after `q` is represented in
`H(S)`. Recording its owner bound and enqueueing the opposite-bound
consequences is the same-row-set transition for which the target is

```text
Sol(H(S_after_record_and_enqueue)) = Sol(H(S_before_record_and_enqueue)).
```

The proof obligation includes the premise that prior stored bounds are true
logical inequalities and that pending, processing and retained replay items
remain in `H(S)` until their obligations have a retained successor
representation.

This D2 slice starts after collection has made the fixed family’s endpoint
rows available and is limited to successful owner-recording branches. Pairs
with no live row owner are not made to look like bound insertions: unequal
non-row Value comparisons and specialized Effect operands take other paths.

## Source path and state ownership

| Boundary | Source behavior and owners | Logical reading |
| --- | --- | --- |
| Authentic fact admission (`lib.rs:11481–11524, 3960–3971`) | `admit_collected_fact` calls `ConstraintTransaction::admit`, then `record_provenance`; every successful receipt maps the term kind to polarized Value/Effect endpoints and calls `constrain_live_value/effect`. `admit` inserts a new `SemanticFact`/canonical `FactId` or returns an existing `FactId` with `AdmissionDelta::Duplicate`; both success branches continue to typed work. | The store insertion is idempotent for a duplicate key, but the corresponding q still enters the live caller/work representation. Model either receipt as `H_after = H_before ∪ {q}`; this may shrink `Sol` unless q was already entailed. This source/work ingress is separate from D2 equality. The occurrence/cause stay attached to the initial typed drain. |
| Initial pending/current work (`lib.rs:14186–14245, 14289–14366`) | `constrain_live` creates `TypedWorkItem`; candidate mode enters `run_candidate_typed_drain` → `start_typed_drain`, which starts a frame and enqueues the item. `step_typed_drain` moves a dequeued item from `typed_worklist` into `TypedDrainFrame.current`, then through Transport, Context and Dispatch. The frame also retains its initial request, designated and saved processing pairs; a popped local remains held before `current` publication. `dispatch_live_item` routes a noncurrent Value/Effect pair through `apply_value/effect_task` to `candidate_apply_value/effect` (`lib.rs:14432–14463, 13729–13737, 16193–16200`). | A pop does not erase the obligation: it remains in the active local/frame representation. `H` includes queue membership, active initial/current and saved processing slots, and caller/local transfer slots. Under the R337 K0 invariant, identity context execution is inert; R336 L0 keeps live rows at one level and excludes copy-origin intrusion. |
| Owner selection and recording (`candidate_extrusion.rs:635–642, 1070–1170`) | For the bounded family where `candidate_apply_value/effect` finds a live row owner, the function canonicalizes endpoints, returns on equality, selects physical owner/polarity, then calls `candidate_insert_bound` followed by `candidate_replay_bound`. Equal-level row→row Value/Effect uses a negative upper bound on the lower row. A row lower endpoint with a non-row upper endpoint uses a negative exact upper; a non-row lower with a row upper uses a positive exact lower. | `candidate_context::bound_pair` (`candidate_context.rs:3311–3321`) interprets positive `(owner,item)` as `item ≤ owner` and negative as `owner ≤ item`. Thus the recorded `BoundKey` denotes the original directed inequality, independent of which endpoint owns its physical cell. Both-row level comparison is settled by R336 L0 (all K0 rows are level 1). Unequal non-row Value endpoints and Effect operands handled by `candidate_check_effect_operand` are outside this owner-recording family. |
| Physical lane and readback (`candidate_extrusion.rs:648–700, 702–875`) | `candidate_insert_bound_with_evidence` canonicalizes endpoints, registers the logical `BoundKey` admission, chooses the Value/Effect lower/upper row/atom vector, appends one incidence, reads the addressed `PhysicalBoundSlot` back as a complete `BoundKey`, checks exact equality, records capture incidence if requested, marks the graph dirty and emits evidence. | Vectors are incidence storage and intentionally can contain duplicates. `H` interprets each entry through its direction; exact readback verifies the selected cell matches that direction. Duplicate slots add no new logical inequality. |
| Opposite-bound enumeration (`candidate_extrusion.rs:878–935, 1070–1085`) | `candidate_opposite_count` snapshots the number of opposite-polarity row plus exact-atom bounds. `candidate_opposite_bound` indexes the matching two-lane concatenation. For positive insertion it enumerates upper bounds; for negative insertion it enumerates lower bounds. `candidate_replay_bound` holds this count fixed for this call. | Each enumerated slot is an existing logical inequality at the same canonical owner. The fixed count bounds this one local generation step only; it does not establish temporal coverage for later mutations or the whole recursive driver. |
| Consequence retention (`candidate_context.rs:126–140, 2369–2403, 3992–4056, 4185–4228`) | For each fresh replay dependency, replay orders the endpoints by polarity, records a Value diagnostic edge where applicable, creates a `ReplayOperation` whose `children` retain relation IDs, then `candidate_context_drive_replay(replay,None)` transfers each child to the typed worklist. An exact existing `Dependency::Replay` key is skipped at line 4054. `replay_operation_queue_next` reads by `queued`; `transfer_replay_child` advances `queued`. Once all retained children are queued but `consumed < children.len()`, the operation returns `Queued` and stays live for the outer consumer. | From generation until acknowledgement, each child obligation remains in `ReplayOperation.children`; after transfer it also has a typed work item, and after dequeue it has a frame/current ack. For a skipped exact dependency, the two owner inequalities still entail the child in `Sol(H)`; whether earlier queue/cache processing fully accounts for every such duplicate remains a separate coverage obligation. The ordinary path does not synchronously drain/ack each child, unlike the serial `Some(provenance)` restoration adapter. |
| Processing and completion (`lib.rs:14313–14333, 14881–14932; candidate_context.rs:2405–2452`) | The outer drain pops each item into `current` and retains its `ReplayChildAck` in `replay_acks`. Terminal acknowledgement calls `complete_replay_child`, advances `completed_acks`/`consumed`, and retires the replay operation only after every child is accounted for. | A dequeued consequence remains in `current` and its ack list. It is not removed from `H` merely because `pop_worklist` ran. Completion occurs after its child typed-drain work and diagnostics stage. |

The ordinary worklist generation and handling owners within the fixed R338
family are `lib.rs` (source admission, typed drain, worklist) and
`candidate_extrusion.rs` / `candidate_context.rs` (owner bounds, replay child
generation and retained transfer). The R337 context lifecycle census covers
context construction and the R336 L0 source/allocator argument supplies the
no-copy/no-intrusion premise. No additional production owner was needed beyond
the inherited eleven-source manifest.

Other bound writers exist in the broader compiler: copied-bound extrusion,
intrusion canonicalization/replay, scheme restoration, and signature/Allowance
construction. They are not silently folded into this family. Under authentic
K0, R336 L0 excludes higher-level copied-bound extrusion and its copy-origin
intrusion; R336/R337's exact source-membership premise excludes local scheme
FreshUse and annotation/operation/primitive signature Allowances. These
exclusions bound this packet; they do not close general N, X, Q, or restoration
coverage. If fresh review finds a K0-reachable writer in these excluded paths,
the census is incomplete and D2 remains open.

## Bounded preservation argument and its limits

Let the just-admitted/current inequality be `c`. For a positive owner bound,
the new lower endpoint `l` satisfies `l ≤ owner`; each enumerated existing
opposite upper `owner ≤ u` yields the child `l ≤ u`. By transitivity, each
child is entailed by the old represented opposite bound and `c`. For a negative
owner bound, `owner ≤ u` and each existing lower `l ≤ owner` yield `l ≤ u`,
also by transitivity. Value uses the fixed K0 preorder; Effect uses transitive
subset inclusion. Equality is discharged by reflexivity before storage.

Therefore adding the owner incidence only re-represents `c`, and adding the
finite generated child set to pending work adds only entailed constraints.
Because duplicates collapse in `H`, a repeated physical incidence or repeated
typed item cannot strengthen this logical theory. By the work invariant,
transferring a child from retained replay storage to typed worklist, then from
worklist to `current`, changes representation only. This establishes the
solution-set equality for the owner-record/enqueue boundary, conditional on
the stated prior-bound and work invariant premises.

This does not prove recursive processing preserves `Sol`, that all eventual
opposite bounds are covered across mutations, that pair-memo/cache suppression
is complete, or that a completed graph represents every authentic source
fact. The `candidate_replay_bound` snapshot is local to one invocation; later
children can create bounds outside its count and require a separate temporal
coverage theorem. No claim is made for all N, W, Z, S0, D3, principality, full
source/native A/B, catalog, or production.

The source does retain a dequeued replay child in `TypedDrainFrame.current`
and `replay_acks` until the typed drain reaches its terminal acknowledgement.
R338 stops before proving the recursive semantic step or the correctness of a
`pair_is_current` suppression hit. Thus the work-invariant premise must supply
that any child removed after processing was already represented or had its
consequences accounted for; proving this for all memo/cache and recursive
interactions is explicitly outside this bounded result. Exact dependency-key
deduplication is also outside coverage closure: transitivity proves that a
deduplicated child does not change `Sol(H)`, but does not establish that every
required processing obligation has already been discharged.

The source-qualified falsifiers are: a successfully reachable owner mutation
whose bound direction disagrees with `bound_pair`; a generated opposite-bound
child that is not entailed by the owner pair and the existing bound; a
dequeue/transfer/ack gap where a logical obligation is absent from stored,
pending, processing, or retained replay state; a separating K0 valuation; or
an omitted K0-reachable mutator. No execution probe, test, Cargo/build, compiler
write, or runtime was used.

## Review and correction record

The independent review used revision 1 of this census, SHA-256
`1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d`, with the
unchanged producer proof `notes/theory/2026-10-23-r338-k0-d1-d2-state-bridge.md`
(SHA-256 `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0`)
and handoff `tasks/agent-loop/inbox/20261023-r338-k0-state-prover.md` (SHA-256
`1ea41023fd18f95343bd5ec69a4af611a010e2d61bf4388fb3b159d224f3cb40`). Review
disposition: D1 composition PASS; post-admission owner-record/enqueue lemma
PASS under its stated premises; MAJOR finding on the unconditional duplicate
admission sentence in revision 1. The reviewer found no source-qualified
reachable K0 counterexample or compiler defect. Luna accepts the finding and
applies the reviewer's minimum correction in revision 2.

Revision 2 models both accepted and duplicate source receipts as ingress of q
into `H(S)`. `Sol` equality at admission is claimed only with a separate
`H_before ⊨ q` premise. This correction has not received delta review, so the
admission transition is not promoted. It does not alter the separately reviewed
post-admission owner-record/enqueue lemma. All broader N, cache/coverage,
W/Z/S0/D3, principality, source/native completeness, original A/B, catalog and
production gates remain OPEN.
