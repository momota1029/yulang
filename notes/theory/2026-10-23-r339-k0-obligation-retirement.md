# R339 — retention of an ordinary K0 bound-replay obligation

Status: **frozen producer candidate, revision 1; fresh review required**.
Assignment `R339-K0-RETIREMENT-D2`; author `/root/r339_obligation_prover`.
No coauthors or descendants. This is a bounded source-based hand proof, not
an independent review, execution observation, whole N theorem or production
authority.

## Parent and exact result

The unchanged parent is the full Yulang2/Simple-sub source/native A/B objective.
The immediate parent is audit N/D2: same-row-set native propagation should
preserve the solutions of an independently interpreted `H(S)`. S0 still needs
that result, the independent K0 source judgment and the actual machine bridge.

This packet launched under R339 revision 1, SHA-256
`e74ea60ec6c9a7fee246fc9bca9ad0bfae2712c291fe570c1f5bbd25f1aac3fc`,
and acknowledged the read, hash-verified sequential governing revision 2 at
`tasks/agent-loop/sprints/r339-k0-obligation-retirement-20261023-rev2.md`,
SHA-256 `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00`.
The amendment adds exact read inputs without changing this scope, lease or cap.
Its family is **one actually emitted ordinary bound-replay child** `q`, from
`candidate_replay_bound` → `candidate_context_begin_replay(...,false)` →
`candidate_context_drive_replay(...,None)`. For every such q in an authentic
successful K0 prefix, its two generating bounds supply an enduring algebraic
witness. Therefore q remains entailed after its cache-current check, after
its replay acknowledgement, and after the containing typed-drain frame is
removed. This holds for either result of the cache check. It does not require
that a cache-hit branch exists for every q, or infer such reachability from a
mock transition.

The conclusion is entailment, not literal work membership. At acknowledgement
the final retained replay copy can disappear, and at frame removal its active
processing copy can disappear. The two actual stored antecedents still imply q.
This proves the q-specific retirement premise for this family, and the entire
single-child acknowledgement step preserves `Sol(H)` under the fixed state
interpretation below. It does **not** prove whole-frame equality for every
other obligation discarded by that frame.

Precisely, quantify over every authentic successful K0 prefix, every actual
ordinary bound-replay child q emitted in that prefix, every subsequent
successful state S in its named same-row-set lifecycle, and every assignment
ρ on that row set. The conclusion is `ρ ⊨ H(S) ⇒ ρ ⊨ φ(q)`, including S after
the child's acknowledgement and the containing frame's removal. Thus the
result includes all actual endpoint values of this family, rather than one
chosen successful model or an assumed queue transition.

## Fixed domain and independent interpretation

Use precisely R336 revision 4's authentic `ValidK0`: ordinary candidate mode,
one nonrecursive definition with empty outer environment, selected-definition
entry, and its seven listed source cases and exclusions. R336 L0 supplies
level 1 and absence of higher-level parent/copy intrusion on successful K0
prefixes. R337 J supplies default flow, no Allowance and identity contexts.
No source restriction, effect-valuation restriction or inference bypass is
introduced here.

Use the R336 finite Value preorder with four-port Function variance and finite
Effect sets over the unchanged universe Ω, ordered by inclusion. Existing
Value/Effect row assignments, representatives and meanings of existing term
endpoints are fixed over the named same-row-set lifecycle. In particular,
symbolic Function effects need not be empty. No model-existence or reification
claim is assumed or proved.

For a same-sort task q=(l,u), let `φ(q)` be the independently defined Value
comparison or Effect inclusion. For a bound key `(o,p,b)`, define

```text
β(o,Positive,b) = b ≤ o
β(o,Negative,b) = o ≤ b.
```

The actual `bound_pair` agrees with this orientation
(`candidate_context.rs:3311–3329`; the equivalent effect-owner helper is at
`candidate_effect.rs:485–500`). Let `B(S)` contain the projection of existing
direct/exact Value and Effect vectors, as well as retained owner-side keys
with attached relations. Use the unchanged R338 interpretation

```text
H(S) = B(S) ∪ Q(S) ∪ P(S) ∪ R(S) ∪ D(S).
```

Q interprets pending typed items. P interprets actual current/initial requests,
pending dispatch items, designated and saved processing pairs/relations, and
live caller/local transfers. R contains `operation.task` for every unretired
ReplayOperation child slot `consumed ≤ j < children.len()`. D interprets
explicit remaining structural-dispatch children. Physical duplicates remain
different incidences; their identical logical inequalities are idempotent in
this conjunction. Inactive memo entries, historical source facts, completion
bits and bare acknowledgement IDs contribute no extra inequalities.

Neither `H(S)` nor its solution set is defined by native acceptance, source
typing or runtime success. Source admission is outside this retirement family.
The unreviewed R338 revision-2 admission correction supplies no equality premise
to the proof.

## Actual constructor supplies the witness

Fix any actual child slot of an ordinary replay operation O emitted along the
path above. Let `o` be its canonical row owner at creation. Source inspection
gives a witness `(bL,bU)` in existing bound storage, with one of these two
orientations:

| Insertion | First stored premise | Second stored premise | Actual emitted q |
| --- | --- | --- | --- |
| Positive | inserted `l ≤ o` | selected existing `o ≤ u` | `l ≤ u` |
| Negative | selected existing `l ≤ o` | inserted `o ≤ u` | `l ≤ u` |

These premises are obtained from physical constructors, not merely from the
`ReplayOperation.inputs` labels:

1. `candidate_apply_value/effect` selects owner/side and invokes insertion
   before replay (`candidate_extrusion.rs:1115–1176`). The bounded R338 lemma
   already proves that the stored orientation represents the incoming pair.
2. `candidate_insert_bound_with_evidence` appends the exact payload to the
   selected direct/exact vector, then reads back and checks the full key
   (`candidate_extrusion.rs:702–875`). A successful return therefore supplies
   an actual stored incidence of the inserted bound.
3. `candidate_opposite_count` and `candidate_opposite_bound` read the opposite
   direct/exact vectors (`878–938`). `candidate_replay_bound` captures a count,
   selects one actual slot, orders the task endpoints according to polarity,
   and orders `lower_input/upper_input` the same way (`1070–1111`). There is no
   appeal to global temporal coverage or unique slot enumeration.
4. `candidate_context_begin_replay` constructs child relations for that exact
   task pair and stores the unchanged task in O (`candidate_context.rs:
   3992–4074`). Its ordinary duplicate-key check can omit a child; this theorem
   quantifies over actual retained/emitted slots and proves no completeness
   claim for omitted slots. R337 J supplies identity/default child metadata.

Consequently, at generation and every later state retaining these two physical
bounds, for every assignment ρ on the fixed row set,

```text
ρ ⊨ B(S)  ⇒  ρ ⊨ β(bL) ∧ β(bU)  ⇒  ρ ⊨ φ(q).
```

The final implication is transitivity of the independent Value preorder or of
subset inclusion. It applies to unequal endpoints, arbitrary symbolic effects
and cyclic incidence. It asserts no finite solution exists. The witness is a
mathematical record of the actual two selected incidences, not a new compiler
certificate or invented operational transition.

## Persistence through the successful lifecycle

The two bound incidences remain present through the ordinary lifecycle under
consideration. The owner insertion path appends vector cells; its physical
readback fixes the payload. Queue transfer, typed processing stages, replay
cursor updates, diagnostic completion and frame removal do not delete those
cells. In particular:

- `enqueue_item` transfers the exact stored task and ack, advances `queued`
  only after preflight, then inserts the item (`lib.rs:15223–15250`;
  `candidate_context.rs:2369–2396`). `consumed` is unchanged.
- `pop_worklist` and Transport move that item into `frame.current`; its ack
  enters `frame.replay_acks` (`lib.rs:15166–15173,14301–14333`). A temporary
  local remains an owner during the transfer. These operations leave B intact.
- Context execution is inert under R337 J
  (`candidate_context.rs:3789–3826`). Candidate-mode apply routes directly to
  the append/replay owners (`lib.rs:13729–13738,16193–16201`). Function
  dispatch creates/queues its selected children (`lib.rs:14705–14870,
  14953–14990`); neither that activity nor a terminal incompatibility removes
  the generating bound vectors. This does not certify that structural child
  addition itself preserves the solution set.
- Empty-queue settling cannot merge K0 rows: L0 supplies no copied-row pending
  intrusion. The empty-pending branch only clears dirty
  (`candidate_intrusion.rs:568–581`). General merge/canonicalization and
  generation change (`694`) are outside this successful K0 family.
- Successful terminal acknowledgement and return touch context/frame/replay
  state, not bound vectors (`lib.rs:14881–14945`;
  `candidate_context.rs:2398–2403,2444–2452`). Replay reclamation removes O and
  its child-storage accounting (`2190–2203`), without removing owner bounds.

This is a forward source-path argument. The actual destructive vector
truncations in `lib.rs:9743–9790` belong to failed-route rollback. Resource
failure/private attempt discard and rollback are not successful retirement
steps, and no preservation or successful-retry result is claimed for them.
Scheme restoration's `Some(provenance)` synchronous adapter is also distinct
(`candidate_context.rs:4160–4183`). The proof does not transfer to that adapter,
to K1, or to a state with representative changes merely because cursor names
look the same.

## Cache check, acknowledgement and frame retirement

**Cache-current check.** `pair_is_current` tests memo membership and whether the
current processing relation has the current generation stamp
(`lib.rs:13507–13518`). `mark_candidate_pair` writes that stamp from
`record_typed_pair_admission` *before* apply/decomposition finishes
(`lib.rs:15338–15340`; `candidate_intrusion.rs:423–455`). Thus the stamp is
not independently a proof that q was semantically discharged.

For the particular q fixed above the constructor witness supplies what the
stamp does not. If the check is true, Dispatch skips apply, then clears the
current copy (`lib.rs:14439–14463,14356–14366`). R still retains q until the
acknowledgement; B also entails q. No logical strengthening occurs on this
skip path, and every deleted q copy is redundant, so this local cache-skip/
current-clear step preserves `Sol(H)`. The Effect branch's evidence admission
has identity/default metadata; a bare new relation is not an extra H formula.
If the check is false, subsequent processing is not certified wholesale by
this lemma, but persistence of the antecedents still proves q at its retirement.

**Acknowledgement.** Terminal code consumes a prepared exact ack, invokes
`complete_replay_child`, then increments the frame counter
(`lib.rs:14923–14933`). The callee checks `operation.consumed==ack.index`, and
the ordinary waiting state is Idle; it advances consumed and may retire/reclaim
O. Cursor validation proves which slot is removed, not semantic entailment.
That slot's formula is exactly φ(q). If there are several slots, all refer to
the same `operation.task`; no separate per-slot inequality is invented.

Let T be the obligations unaffected by that single acknowledgement step.
Both generating bounds belong to T. Before the step H is `T ∪ {q}` or T if q
already has another copy; afterwards it is T or still `T ∪ {q}`. Since
`T ⊨ q`, these theories have identical solutions. This proves the exact
single-child acknowledgement/operation-retirement equality without using a
completion bit as a premise, even on the final child.

**Frame retirement.** ReturnReady may publish passive source completion, then
pops the frame and restores its exact saved processing pair/relation
(`lib.rs:14935–14945`; `candidate_effect.rs:502–511`). The two B premises
survive, so `H(S_after_pop) ⊨ q`. This applies if q had its last active copy
in processing state; it does not count the retired operation or completion
receipt as a retained q.

The popped frame can also own a distinct initial request r, a designated live
processing pair, and a live processing relation different from q. Saved
previous processing slots transfer into the restored live slots. Preservation
of the *whole* pop step requires every other removed live formula to be
entailed by the remaining theory. The present q witness supplies exactly the
q instance and does not discharge those independent instances.

## Application and remaining owners

R338 established entailment when this ordinary replay q is generated. Applying
the same actual antecedents through the inspected consumers now discharges its
retirement premise: the q conjunct can be removed at cache suppression,
acknowledgement and eventual frame removal without losing q's consequence.
This is a genuine extension past R338's before-child-solving stop boundary.
It does not assume recursive child solving is globally preserving.

The exact residual whole-frame premise is

```text
for every other r removed from P or D at this pop,
    H(S_after_pop) ⊨ φ(r).
```

The first owners to distinguish are source `frame.initial` ingress/dispatch
(`start_typed_drain`, `dispatch_live_item`, `lib.rs:14186–14245,
14432–14870`), Function-port children that lack this *direct* bound-replay
witness (`candidate_step_function_dispatch`, `14953–14990`, and
`candidate_function_port_admit`, `candidate_context.rs:3505–3568`), and
processing restoration (`candidate_step_typed_drain_terminal`,
`lib.rs:14935–14945`). A valid cache hit for one direct replay q does not prove
cache validity for every relation or any temporal/fiber coverage theorem.

`R339-D2-REVIEW`: Luna freezes this artifact and appoints a fresh non-contributor
to challenge antecedent persistence, exact task/ack identity and the distinction
between q-specific retention and whole-frame equality. Inputs are the pins
below; output is a disposition on this exact family. Falsifier: an authentic
successful K0 instance of the named ordinary producer/consumer path with an
absent/reversed generating bound, changed task, or a post-retirement valuation
satisfying H but falsifying q.

`R339-D2-REMAINING`: Luna owns assignment of the residual per-formula retirement
inventory at the owners above. Required evidence is the actual incoming source
or Function-port construction, not its completion label. Proposed output is
an exact retained representation/entailed witness for each removed formula, or
a source-qualified separating valuation. This TODO grants no new lease or
production authority.

`NO_SAFE_CODE_SLICE`: both the dispatch/cache owner in `lib.rs` and replay
completion owner in `candidate_context.rs` were inspected. No source-qualified
compiler defect was established; no provisional implementation is needed for
the proved q instance. Broader N/cache coverage, W/Z/S0, D3/M, reification
existence, original A/B, catalog and production remain OPEN. F1/FK1 and other
foreign-continuation quantifiers are neither used nor discharged.

## Frozen dependencies, provenance and checks

All current byte hashes below were directly checked. The branch/head
`research/simple-sub-intrusion` / `f647390d6a3502c0d8814d46870d55685cee1753`
and compiler baseline `17e57af2c4605d7084c7d76792b115674776bbe2` are supplied
contract metadata, not worker Git observations.

| Input | SHA-256 |
| --- | --- |
| Governing R339 sequential rev2 contract | `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00` |
| User audit named above | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R336 rev4 contract | `080ab51650f88ddb7030e2a9bcb0ebfc9cc9b62de29204910e888365f7d03118` |
| R336 rev4 integrated proof | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R336 independent review | `d03b7a23bcec2bd0575bf391342f92353b46b840cbcfa70deea7500786fd892e` |
| R337 contract | `0d71e3c740aa3d48667e3a9d62d15b835084a432e394fe79cc30d2b9d4cc9a3e` |
| R337 context proof | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` |
| R337 context census | `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a` |
| R338 contract | `d742fa449c81b8b3cc918f53f93fc462dccb98565a2ed817e0b64162919ee403` |
| R338 proof | `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0` |
| R338 census current rev2 | `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9` |
| R338 census rev1 immutable review snapshot | `1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |

The final source owner is an inherited R337/R338 pin, reached here specifically
for designated processing/restoration and enqueue evidence; Luna was notified.
The R338 reviewed census rev1 bytes were read and hash-verified at
`tasks/agent-loop/review-inputs/r339-r338-census-rev1.md`; they differ from the
current rev2 census. The separately allocated 150-second admission delta review
ended OPEN/incomplete, as governing R339 rev2 records. This producer does not
complete or certify that independent review. The proof uses the common H
interpretation and independently inspected named source steps, with no
admission equality from either version.

Reused results: R336's algebra/L0 under authentic K0 premises; R337's J under
the same successful-prefix premises; R338's owner orientation and emitted
consequence lemma. Rejected inference: completed/duplicate/cache/source-store
labels imply entailment. No historical general restoration, F1/FK1 or
FieldTail result is imported beyond its premises. Prior proof authors are Luna
`/root` and `/root/r336_k0_algebra_prover` for R336/R338, and
`/root/r337_k0_context_prover` for R337; the censuses are Luna-authored.
R336 independent reviewer is `/root/r334_fieldtail_review`; audit author
identity is UNKNOWN. These authorships do not certify this new result.

Checks: direct read-only source inspection, SHA-256 comparisons and manual
algebraic reasoning. The attempted `python` hash helper was unavailable
(`python: command not found`); direct `sha256sum` succeeded. No tests, builds,
Cargo, executable/compiler/runtime probes, external contact, Git or descendants.
Only this artifact and the exact assignment inbox are new paths; no scratch
files. Requested role/model/effort: prover / gpt-6.1-sol / high. Observed
effective model/effort: UNKNOWN / UNKNOWN. Actual task identity is
`/root/r339_obligation_prover`; opaque host session ID is UNKNOWN. Current
NEW_TASK delivery is the launch receipt; first clock receipt
2026-10-23 05:27:52 UTC. The fresh 1,200-second grant is charged in full
conservatively; no carryover/renewal. Exact freeze/STOP receipt is in
`tasks/agent-loop/inbox/20261023-r339-k0-retirement-prover.md`.

The producer stops writing at the frozen handoff. No independent certification
or parent promotion is claimed, and no worker remains computing while review
waits. Luna owns fresh review, adjudication and integration.
