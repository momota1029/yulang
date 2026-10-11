# Oracle direct: canonical replay and projection census boundary

Date: 2026-10-11
Status: frozen, unreviewed research source characterization; original H OPEN
Claim class: local key/duplicate derivation and precise incomplete operational census
Y3 pinned baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`
Branch supplied by primary: `research/simple-sub-intrusion`
Oracle read root: `/tmp/yulang2-oracle-read`
Oracle revision rechecked: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation

## 1. Objective and unchanged gate

Attempt the exact static canonical-result and projection-ledger census for:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

The original universal H is fixed by
[global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. Authority is [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2, including its withdrawn-example boundary in §6, subject to
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. No semantic choice, source restriction or implementation follows here.
H still quantifies over all original successfully lowered sources, composed-negative
occurrences, original scopes/binders, actual copies and actual call/output routes.
Its instance-local subtraction, independent contribution survival, connected tails,
current/future checks and correlated lineage conclusions remain unchanged.

Use A, C, Y, O, s and r_Y with their constructor meanings in
[native lower follow-up](../theory/2026-10-11-oracle-direct-static-liveness-followup.md)
§§2–3: annotation Function A, formal variable C, skeleton body/result Y,
skeleton output O and original stack ID s. The proven A/s→C and C/Y→r_Y
transport is an input. This pass addresses its remaining §4 census; it does
not repeat that transport or the Incomplete-versus-terminal result.
The inputs also include the [owner audit](2026-10-11-oracle-direct-projection-owner-audit.md),
[direct liveness note](../theory/2026-10-11-oracle-direct-liveness-proof.md) and
[scheme identity note](../theory/2026-10-11-oracle-annotation-scheme-identity-proof.md).

Hypotheses for the local derivations below: pinned source bytes, arena-local
structural interning, completed nonterminal owner calls and no ID exhaustion.
No hypothesis supplies the final admission prefix, a budget outcome, completed
projection transaction, compact liveness or numeric identity from displayed `#0`.

## 2. Exact result keys and a later duplicate route

Oracle locators in this note are relative to its read root. `poly::TypeArena`
interns Pos and Neg structures (`crates/poly/src/types.rs:676–692`). Consequently
every allocation of `Neg::Var(Y)` in this arena yields the same NegId n_Y;
the analogous fact holds for PosVar(Y), PosVar(O) and NegVar(O). Fresh TypeVars
and structural node interning are different operations.

`constraints/machine/entry.rs:1092–1119` canonicalizes a comparison to
`SubtypeConstraintKey { lower, upper, weights }`. It drops Bot/Top and same-var
comparisons, erases weights only at terminal endpoints, and normalizes weights
only for Var/Var replay. A is a Function and n_Y a Var: the designated empty
comparison therefore has the exact key

```text
K_AY = (A, n_Y, empty ConstraintWeights).
```

Its ConstraintRecordId is the value of `canonical_constraints[K_AY]`, allocated
from the constraint-record vector on first insertion. The lower-bound key is
different: `BoundSemanticKey::Lower { owner:Y, endpoint:A, weights:empty }`
(`constraints/mod.rs:2420–2439,2511–2606`). `lower_record_for_constraint`
(`machine/bounds.rs:2304–2330`) first consults the explicit projection-target
index; only when absent does it use that bound key, derived from the result's
NegVar target. Constraint and Bound record numbers are not interchangeable.

There is a concrete later candidate already in this source construction.
The selected empty-predicate skeleton creates Y <: O and O <: Y before the
body's C <: Y (`lowering/expr/lambda.rs:1190–1218,790–810`). The helpers allocate
interned Var endpoints (`lowering/expr/constraints.rs:96–121`). Thus, under
successful generic replay of these uncovered alias routes, the following
additional pair returns to the exact K_AY:

```text
r_Y : A <: Y
U_YO : Y <: O       ⇒ K_AO, lower r_O : A <: O
r_O : A <: O
U_OY : O <: Y       ⇒ K_AY again
```

Empty replay weights compose to empty at these pairs. Both uppers exist before
the body emits C <: Y: `ConstraintMachine::subtype` drains after enqueue
(`entry.rs:493–500`). Their NegVar endpoints are not the row-reduction producer
shape. This extension uses the same production replay and coverage facts as
the inherited local lemma, rather than adopting a new graph grammar.

The binary carrier returning from O has `pivot:O, lower:r_O, upper:U_OY` and
`rule:LowerBoundAdded` when consumed in that ordering. It differs from the
initial C-pivot carrier even though the resulting canonical comparison is
identical. The local key result is established from constructors and interning;
retention of that carrier, its exact parents and final ledger consequences
remain conditional on the real replay/admission transactions. This is a
minimal source-derived reason that the first K_AY admission is insufficient
for the final census. It is neither an H counterexample nor a completed
inventory of all program-generated comparisons.

## 3. Admission and ledger keys that the census must evaluate

The following table covers the inspected production admission families and
their canonical lookup/merge seams. It does not assert that every family is
reachable for K_AY in this source.

| Admission family | Result lookup and duplicate behavior | Relevant ledger consequence |
| --- | --- | --- |
| Ordinary root (`entry.rs:1357–1426`) | Same subtype key; root OriginId dedup by equality; duplicate does not enqueue | New root calls `register_constraint_projection_carrier_delta`; explicit late origin attachment at 505–535 does likewise |
| Structural (`1432–1595`) | Same key; `StructuralDerivation { parent, rule }` dedup; secondary merge requires existing key | Inherits actual parent result's canonical qualified parents; `bounds.rs:1923–1960` handles inserted carrier or ClaimsOnly delta eagerly |
| Row (`1630–1711`) | Same key; RowDerivationId dedup; row definitions intern rule, ordered parents and retained items | Row carrier needs the separate `register_reduction_route_claim_parent` call (`bounds.rs:3118–3158`) for its qualified-parent delta; row enqueue alone is not that operation |
| Binary replay (`entry.rs:1165–1289`) | Same key; BinaryReplayDerivation equality includes pivot, lower/upper BoundRecordIds and rule | Accepted retained edge, including an exact duplicate edge, can admit new side-qualified parents; metadata duplicate is not a final ledger no-op |
| Prefiltered replay (`bounds.rs:4064–4115`) | Uses the already existing canonical key; calls `merge_replay_derivation` | Non-Incomplete disposition invokes qualified-parent registration with `materialize_existing_target=true` |
| Delayed duplicate in normal replay (`3832–3890`) | Key may become occupied after action preparation; same merge path | `!enqueued` enables the same eager materialization |
| Completed scheme route (`entry.rs:757–813`) | Per-record exact route/derivation equality; only empty remaining path becomes a completed carrier | Adds `SchemeInstantiationConstraint { result, source_witness }` and an eager carrier delta; unfinished route storage alone is not a support |
| Direct/evidence lower (`entry.rs:730–754`; `bounds.rs:3907–4062`) | Bound key includes owner, exact endpoint and full weights; ordinary admission may promote Evidence state | New bound derivation or evidence carrier can alter an existing ledger; evidence-only replay requires Var/Var and cannot directly be the A/Var comparison |

For K_AY itself, Function lhs rules out the Var/Var normalization and
evidence-only branch. The Function lower also bypasses lower alias-cycle
subsumption. Those exclusions do not eliminate other records' session-wide
budget charges, or replay through alias bounds into K_AY.

Qualified-parent dedup is a third identity layer (`proof/mod.rs:4850–4854,
13139–13212`): `(result, coverage_root, identity)`, with Replay identity
`(parent_side, full binary carrier)`, Structural identity its derivation,
and ReductionRoute identity including its parent claim. Replay incidence
uses `(result, carrier)` and side/root membership (`11973–11998`). Canonical
parent iteration selects a representative per root, ordered by coverage root,
carrier, side, parent claim (`13593–13608,14703–14719`); it is not the exact
qualified-parent inventory. Replaying the same binary edge can therefore add
an unseen root or side without storing another binary edge or queueing work.

`register_cpk_replay_claim_parents` (`bounds.rs:2916–3053`) requires a retained
edge, prepares/commits qualified parents, precommits clause work and, for a
duplicate, materializes the existing target before publishing its fence.
`register_existing_constraint_lower_projection_delta` (`2373–2420`) bootstraps
from all canonical parents if no ledger exists; otherwise it uses the admitted
delta. `register_lower_projection_delta` (`2480–2569`) returns early only when
both incoming claims and existing ledger are absent. On bootstrap it scans
all bound derivations; with an existing ledger it classifies the exact delta.
Independence consults the current claim ledger and qualified-carrier incidence
(`2600–2720`). These are actual state reads that syntax alone has not instantiated.

Support equality uses a coverage-root-normalized Claimed key or an exact
Independent carrier (`constraints/mod.rs:798–867`; `proof/mod.rs:5870–6010`).
Formula membership instead uses the raw support group, exact RecordProofClause
and exact support/clause incidence (`proof/mod.rs:7652–7690`). A replay clause
contains its full carrier and both bound premises; Structural is unary in its
parent constraint; ReductionRoute is unary in its coverage root
(`bounds.rs:1180–1247`). Distinct carriers for K_AY need not collapse to one
formula arm even when supports normalize to the same root. No count of claims
or uncovered-support payload can substitute for this incidence census.

## 4. Exact unresolved prefix and collection operation

The first still-uninstantiated retention operation is the actual
`enqueue_replay_subtype(K_AY,d)` entry lookup, followed by its vacant or
occupied budget check (`entry.rs:1178–1218,1262–1277`). Its necessary inputs are:

```text
canonical_constraints[K_AY] before admission;
that result's retained replay_derivations before admission;
B = replay_derivation_storage.bytes_proxy at that operation;
M = replay_derivation_budget.max_bytes_proxy;
I = replay_derivation_budget.max_incoming_per_record.
```

This pass does not select a branch from defaults or the source's small size.
The complete inspected charging-owner census gives, initially from zero:

```text
B = size_of(BinaryReplayDerivation) × (retained canonical replay edges
                                      + newly retained evidence bound sides)
  + (2×size_of(ReplayDropRecord)+size_of(ReplayDropRecordId)) × unique retained drops.
```

Owners are `entry.rs:1208–1213,1271–1287,1291–1307,1331–1332` and
`bounds.rs:3907–3927`. A duplicate retained binary edge charges zero; a new
edge to an occupied result checks its new incoming count. A retained trivial
drop charges the session even though it has no result record. Evidence sides
charge according to actual bound-derivation novelty. The accounting expression
is source-derived, but its event counts and the platform `size_of` values at
the designated prefix are not supplied by the retained artifacts. No numeric
proxy or incoming-count census is claimed.

Even resolving that first branch would leave the O return-loop carrier and
every further same-key carrier admission to enumerate. At each actual scheme
collection, the decisive operation is
`scheme_projectable_lowers_in_scope(Y, round)` (`structural_kernel/access.rs:862–898`)
→ `LegacyOnlyReadView::project_lower` (`access/legacy_read_view.rs:238–244`)
→ `proof/mod.rs::project_lower_inner` (9993–10127). Its first support/formula
reads require the final r_Y ledger at that invocation, not at first admission.
With both present, preflight must validate all reachable facts, and formula
evaluation consults both replay premises (`11632–11790`) and their current
coverage roots (`11882–11906`). The exact returned decision and evidence remain
uncomputed here. Unclaimed/Included reach collection, Excluded does not;
this source's actual alternative is not selected in this note.

The retained executable artifact
[callback projection probe](2026-10-11-oracle-callback-reuse-projection-probe.md)
reports formatted schemes, exit code and diagnostics. Its input additionally
contains `through`, `route` and their uses. It retains neither construction IDs,
canonical map, prefix charging events, qualified parents, bound derivations,
support/formula incidence, coverage snapshot nor this projection return value.
Even its containing the direct definition does not establish state equality
with this smaller four-definition source at the relevant boundary. The other
listed notes explicitly leave these facts open. No existing retained artifact
instantiates the missing lookup/budget/ledger inputs.

This is an incomplete bounded static derivation, not a theorem that deterministic
source code cannot in principle be evaluated statically. A full hand evaluation
of the actual lowering/settlement/prepass prefix could supply those counts and
maps. That evaluation has not been completed; a checker supplied with those
transitions or one chosen budget branch would still assume the missing premise.

## 5. Finalization and cleanup boundary

The ledger does not freeze merely because the source constraint queue drained.
`analysis/session/generalize.rs:57–179` collects a compact root and then can
apply merge and interval subtype constraints, route events and restart collection.
Alias expansion and stack cleanup can each supply a bounded further subtype
batch (`491–543`). Their exact emitted batches for direct are uncomputed.
`compact_root_for_generalize:580–603` caches by root and constraint epoch;
cache existence alone is not evidence for this source's final collection snapshot.

`analysis/session/instantiate.rs:14–83` generalizes every component root before
capturing witnesses and finalizing/installing schemes. The ancestor finalizer
changes the exported compact representation; no inspected call there clears
canonical constraints, replay edges or the lower ledger. Source reads found no
production reset of these tables between the designated replay and collection.
The inspected tombstone writer (`bounds.rs:4326–4357`) prunes upper row bounds,
not r_Y's Function lower. Upper-claim rehoming and coverage changes remain
possible premise mutations (`proof/mod.rs:7490–7585,13050–13121`); coverage
deactivation's machine wrapper has only test callers (`constraints/mod.rs:1550–1570`).
These facts exclude a simple automatic lower-ledger reset explanation, while
leaving the actual coverage and upper-record lineage census open.

Do not silently infer the prepasses' batches are empty because direct has no
body call, or infer that a final installed type serializes this ledger. Compact
cleanup/selection and later use remain distinct downstream gates. This packet
does not derive the actual installed selector, provider replay or output lineage.

## 6. Outcome, checks and scope

The new concrete result is the exact-key Y→O→Y return route and its distinct
candidate replay carrier, plus the admission/ledger dedup and lifecycle seams
that prevent first-admission state from serving as final state. The full static
census is **not closed**. The precise residual is the actual operational prefix
needed to instantiate the K_AY lookup and byte proxy, all later qualified/carrier
admissions to its r_Y target, generalization-generated batches and the collection
projection return. H remains OPEN; no source-qualified counterexample exists here.

Under compiler-engineering's proof-obligation-economy rule, H remains A/B;
reconstructing unretained per-record facts from a display is D. A further
freshening lemma, presence-only toy checker or larger display-only probe would
leave this residual untouched. No new implementation or instrumentation is
authorized by this finding.

Checks: bounded `rg`, `sed`, `cat`, read-only revision/status queries and SHA-256
dependency snapshots. Some combined captures were truncated and decisive seams
were reread narrowly; guessed `analysis/session.rs` and `analysis/session/settle.rs`
paths and one Oracle source read issued from the Y3 root were missing and supplied
no evidence. The final note received a read-only whitespace/fence/newline check.
No Oracle invocation, build, test, instrumentation, compiler edit, executable
model, mutation search, formatter, child delegation or Git mutation occurred.
Seeds/ranges/mutations: none. Heavy processes and execution samples: zero.
At most four lightweight independent read commands ran concurrently; CPU/RSS
and total wall time were not instrumented. No numerical time budget was supplied
in this leaf packet. Live model/effort metadata was not observed.

This inspection shares the pinned source and inherited source-route premises
with the prior constructive note. It has no independent execution oracle and
does not certify its own result. Incomplete searches are the complete lowering/
settlement/prepass prefix and all same-key admission enumeration. Unverified:
the final ledger/coverage/formula, projection decision, compact survival,
installed selection, actual use/provider/output bridge and universal H.

Recommended next action: primary adjudicates this exact state obstruction and
records the unresolved admission-prefix/collection premise under its existing
owner. Keep the exhausted invocation budget explicit; do not schedule another
equivalent transport or assumed-transition probe as closure.

## 7. Dependency snapshot and commit packet

Read dependencies were not changed. SHA-256 snapshots:

| Y3 dependency | SHA-256 |
| --- | --- |
| Original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Native lower follow-up | `5b0d56da9df4d11c9fc4959451df6b2b30ba92327a278ec866c65a9d334a1af3` |
| Projection owner audit | `4ffba49b46626787f0c5cde12e72d94996f7bf68cf18c0dbcb7cadc923f75c59` |
| Direct liveness | `eeb4a6bc838fdbc1007cc2565e6654cf382f1c77d65583e318d74e2d8a4bcb8f` |
| Scheme identity | `cd9ec15a679c456d81e35a8d9c977a9ddf11bc5f00579b7909e917424d71d215` |
| Retained callback probe | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| Hygiene authority | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

| Oracle dependency | SHA-256 |
| --- | --- |
| `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `crates/infer/src/constraints/structural_kernel/access/legacy_read_view.rs` | `d51ab100c247f34ccf94cd75af2c28e1bf845a9b1a8719780843b02ba2bd35a6` |
| `crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Commit packet for the primary:

- Exact lease: `notes/progress/2026-10-11-oracle-direct-static-projection-census.md`.
- Baselines: Y3 `d8c097e1f810fb26a8cf1936aa97059f6948bf32`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none observed; snapshots above are the read inputs.
- Review: frozen producer artifact, independent review pending; census and H OPEN.
- Checks already run: static owner/key inspection, revisions/status/hashes and note integrity; zero execution/build/test.
- Proposed one-line checkpoint message: `research: trace Oracle direct duplicate replay and projection census boundary`.
- Shared-record deltas intentionally left to primary/curator: add the same-key Y/O return-loop candidate and exact canonical/bound/parent/support/formula identities; retain actual admission prefix, generalization batches and collection decision as unresolved, with exhausted Oracle invocation budget. No shared task/index/authority record was edited.

Writes stop before frozen review.
