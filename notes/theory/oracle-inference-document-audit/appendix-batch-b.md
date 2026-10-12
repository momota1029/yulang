# Oracle document audit: appendix batch B

Date: 2026-10-12
Status: unreviewed research coverage checkpoint; eight complete reads, three pending
Method: pinned document reading and document-only history inspection
Baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: primary's bounded document-first historical audit packet
Implementation, tests, builds, runtime probes and semantic adoption: excluded

## 1. Coverage and source identities

All historical locators below mean `BASELINE:notes/design/<filename>`.
Line numbers were obtained from that exact blob with `nl -ba`; complete reads
used consecutive bounded `sed` chunks without output truncation. READ means
the text was read, not that its mathematics or implementation was certified.

| Filename | Lines | Pinned Git blob | Coverage |
| --- | ---: | --- | --- |
| `2026-07-21-constraint-provenance-redesign-spec.md` | 1090 | `910b0391ec3f0e9897e632ebb445dd3d7fccbe17` | READ 1–1090 |
| `2026-08-02-mpc-dpn-projection-evaluation-round.md` | 628 | `ec7d8df6cd093a427b3a044858d4a95436c99ee4` | READ 1–628 |
| `2026-08-02-replay-claim-parent-factorization.md` | 2106 | `4861ae800c62ffbd21e3675e6eed00a177c0740a` | Metadata/history only; full body pending |
| `2026-08-03-rcpf-d-materialization-projection-addendum.md` | 1326 | `c0ad9b2f271347d54d3d96ae9829202277eab14d` | Metadata/history only; full body pending |
| `2026-08-04-mutable-reference-act-template-instantiation.md` | 582 | `bd492bf99cf1260f83b604ccb86f599462d2adc0` | READ 1–582 |
| `2026-08-05-constraint-proof-kernel-separation-plan.md` | 959 | `eb369643f624226f5e487f4329e98af7aba49fd8` | READ 1–959 |
| `2026-08-05-cpk-0-projection-admission-addendum.md` | 1591 | `4800e3f19687d397a2a4edbcf50c705776272337` | Metadata/history only; full body pending |
| `2026-08-05-rcpf-e-clause-link-attribution-and-ordering-addendum.md` | 315 | `c647366eabad604894ffdb45b4edec5f21659219` | READ 1–315 |
| `2026-08-06-cpk-7-route-endpoint-decoupling-addendum.md` | 373 | `b82dade21bafdfc1d165fde35e3a7fa62b7dff7f` | READ 1–373 |
| `2026-08-06-cpk-projection-decision-addendum.md` | 978 | `76896ce7d6f665804c92bd8fd416797407474824` | READ 1–978 |
| `2026-08-06-cpk-replay-routing-decision-addendum.md` | 1135 | `b74806ad3113073d235d4f8ad029fbe8e67d9885` | READ 1–1135 |

This checkpoint reads 6,060 of the assigned 11,083 lines completely. The
remaining three bodies total 5,023 lines. The already separately leased
`2026-07-31-claim-parent-delta-materialization.md` was not read or written by
this packet. No unread body is promoted through a later document's quotation.

## 2. Creation, revision and deletion evidence

The filename dates agree with declarations in the eight fully read texts.
Declared dates of the three pending bodies are not independently confirmed
here. Creation uses exact ADD evidence, not inferred rename lineage. Author
and committer timestamps agree for all eleven ADD commits; times below are JST.

| Document abbreviation | Exact ADD commit | Creation timestamp | Later in-baseline revisions |
| --- | --- | --- | --- |
| CPROV | `6c0a01f2f98ef8e8a5039f580af512694b924059` | 2026-07-21 20:34:15 | `e7a71fb7b`: replay storage bounds; `33a6fab42`: row hyperedges/dispositions; `45ddd8502`: incomplete OCAST fail-open decision, July 22 |
| Evaluation round | `ab51980685de813bb61f161c2f20cf618e23a28d` | 2026-08-02 04:30:33 | None |
| RCPF, pending | `5fe43c1ba970287341d6e3c7ae23a8c27daf136e` | 2026-08-02 11:34:10 | `7594f331d`: admission order; `269a84c66`: E closure; `bece72973`: F gap discovery, August 5 |
| RCPF-D, pending | `a8b108100db108b51f67faa0f85a9a29d9370247` | 2026-08-03 10:57:22 | `87afed201`: cross-kind representative; `77faba6da`: ordering stop; `59650fd4a`: canonical inter-root order; `aac375da2`: upper claim order; `c1df9f396`: closure/performance record, August 4 |
| M1 template | `0dc5bd94aec103f7eee857893f8a29ee70e40fb7` | 2026-08-04 13:24:18 | `4c5fe6229`: user expanded scope; `cdb333c62`: cold/sub-label investigations; `d32081e6b`: M1-0–9 closure |
| CPK plan | `f2e491f067c611826b6c8fd2d6729f15a01fcb21` | 2026-08-05 20:11:54 | `70ea51ac158dd60be5f15043228bcdeb0d92c1f6`, 20:14:28: explicit approval |
| CPK-0, pending | `89a6de2289079c42a85d788fefa98ad19c50d5d1` | 2026-08-05 20:57:21 | None |
| RCPF-E attribution | `02050929ed9173919c6177f00e5c73df653b2e24` | 2026-08-05 02:19:49 | None |
| Endpoint decoupling | `43fe00128ef0884417c4f2fe5d86a86e11567fdf` | 2026-08-06 21:38:33 | None |
| Projection decision | `0ceb9308986bba55a7811115c30767fe30074323` | 2026-08-06 08:00:53 | None |
| Routing decision | `10501feaa3b2c54617d0142cafae601c30ef7219` | 2026-08-06 18:38:48 | None |

The inspected all-ref path histories show no rename of these exact paths.
Their later path history records clean-slate deletion at `9f03827ff`, August
18 09:44:25 JST. That deletion is branch/freeze history, not proof withdrawal
or refutation. Revision bodies were inspected narrowly for CPROV's final
policy and CPK's approval; other revision summaries above are log evidence,
not a claim to have read every intermediate version.

## 3. CPROV: forward evidence, eligibility and honest incompleteness

Source: `2026-07-21-constraint-provenance-redesign-spec.md`.

Approval: lines 1088–1090 record user-approved reference specification July
21; this expressly does not authorize any implementation slice. The opening
status preserves that boundary (5–8). Later inline resolutions are distinct
from blanket project completion.

Definitions/invariants:

- `SubtypeConstraintKey = (lower, upper, weights)` remains the semantic key;
  provenance cannot enter Hash/Eq, queue admission, semantic progress or
  termination criteria (§4.1–2, 207–244).
- Stable fact IDs and typed edges preserve alternate duplicate derivations,
  exact replay `pivot/lower/upper`, bound promotion, pruning/tombstones, row
  multiparent contributors and subtract-fact ownership (§§5,7).
- Canonical semantic nodes may form cycles even where the occurrence edges
  reference pre-existing witnesses (§4.5, 268–277). The document does not
  license allocation order as a universal causal rank.
- An eligible source relation must be preserved through the correct typed
  proof chain. A reachable source span or incidental coexistence of lower
  and upper endpoints is insufficient (§6.1–2, 379–413).
- `EligibleSourceBoundary / InternalOnly / Incomplete` classify whether cast
  resolution applies; they do not replace `Missing / Unique / Ambiguous`.
  Quiescent classification must see late duplicate provenance (§6.3).
- Session cap: 64 MiB logical replay-byte proxy and 4,096 incoming replay
  edges per canonical record (§9, 727–748). Exhaustion retains existing
  edges, marks incomplete detail and preserves semantic work.

Correction: `45ddd85022ce494a4316600ec82c567bf927c796` explicitly resolves
incomplete/unknown OCAST evidence as fail open, preserving permissive
behavior (§10 CPROV-J, 923–938; §13.8, 1041–1045). Its reason is avoiding
rejection of legitimate programs with truncated/imported/unwired provenance;
the reported acceptance corpus has zero Incomplete. This is a scoped
historical policy accepting a residual cast-check gap, not a proof of sound
acceptance for arbitrary incomplete inputs.

Proof status: staged executable contracts, required coverage and reported
measurements. No full source-soundness, principality or whole-inference
termination proof appears. Append-only evidence explicitly does not prove
selective origin subtraction or truth maintenance (§1.3, 87–106; 1084–1086).

Dependencies: ordinary-cast resolution spec, two-stage lifecycle's rejected
provenance subtraction, source-origin constructors, quiescent consumer,
complete structural/replay/row ownership and budget semantics. Reuse exact
construction evidence and separation of semantic identity from alternate
proofs. A successor must prove its own source eligibility and consumer
correspondence; historical incomplete OCAST permissiveness cannot authorize
incorrect typing under October 11 principles.

## 4. MPC/DPN evaluation round: the cycle memo restriction

Source: `2026-08-02-mpc-dpn-projection-evaluation-round.md`.

Approval: declaration and ending record user approval (5, 628); no separate
approval timestamp beyond the dated August 2 document/landing is supplied.
Dependencies: MPC, DPN, DPN cycle addendum and already implemented A1/A2,
with investigation baseline `9328d043` (7–22).

Defines immutable evaluator-read snapshot, evaluation view including fixed
overrides, top-level query, round and natural-event atomic clause-link batch
(§2, 76–131). Atomicity means no consumer-visible partial commit, not generic
rollback. A1 exact links do no work; A2 avoids recursive evaluation only
when the proof vector changes and clause evaluation remains fixed (§3).

The smallest documented memo witness (§5, 224–239) is:

```text
source = cycle-arm OR independent-arm
dependent = source
cycle-arm = dependent
```

Starting at source can leave dependent's cycle-context `Done(false)` before
source becomes true through its independent arm. Reusing that memo for a
later dependent query differs from fresh evaluation. Thus a cycle cut
permanently disables cross-root memo sharing for that round; later roots
receive fresh evaluators. Acyclic Done sharing remains permitted (241–269).
This is a discriminating derivation under the documented evaluator rules;
it does not prove source generation of the graph or the complete evaluator's
query-order invariance.

Bounds: O(V+E) for an acyclic round only; after a cut, each fresh query has
its own O(Vq+Eq), without a global linear claim (§8, 382–408). One nonempty
K-link batch uses before/after once each rather than 2K evaluations. Epochs
reflect the net event, separate metadata and inclusion flips (§§6–7).

Historical metrics are explicitly approximate where raw logs are unavailable
(29–44). Regression gates use fresh/shared evaluation and sequential final
ledger as references. They share evaluator/ledger semantics and do not
independently validate source soundness. Reuse the scoped memo/batch method
after proving the actual successor graph and snapshot contract; do not
transfer the old cycle guard as a source theorem.

## 5. M1 typed templates: fresh nominal identity with retained typed bodies

Source: `2026-08-04-mutable-reference-act-template-instantiation.md`.

Declared completion: M1-0–9 landed/verified August 4 (§7, 501–582). User
decisions explicitly widen the scope to cold/no-prefix and sub-label copies,
and select legacy CST fallback on eligibility misses (§6, 459–499). The
earlier proposal wording in §4 is preserved beneath the later completion
record; it is not evidence that activation never occurred.

Definitions: `NominalActTemplateIdentity`, namespace-closure substitution,
typed captured template and detached instantiation product (§3.1). Source
family and operation paths are fresh per binding; internal body IDs are
remapped; external anchors stay external. `label_sub` includes a nested
nominal label and both local return and canonical external
`std.control.flow.sub.return`, requiring a full local/external partition
(85–157). Ordinary scheme cloning alone does not rename nominal families.

Warm capture and embedded cold bundles feed the same validated catalog and
commit lifecycle. Bundles are generated through legacy lowering with typed
instantiation disabled, mitigating self-generated reference contamination;
custom/stale std falls back. Early partial analysis was rejected because
forward-reference/SCC/dependency closure would require scheduler redesign
(§3.3). Invariants cover family isolation, graph closure, type/subtract
freshening, pre-drain finalized installation and detached validation (§5).

Evidence class: reported finite parity tests and performance, not a generic
type/runtime translation theorem. Warm release medians over five runs:
var 27.139 ms → 0.237 ms; label_sub 2.857 ms → 0.359 ms (539–546).
Reported independent fixes are relative external reference resolution and
edge-only placeholder SCC handling (548–564). Mechanism 2 replay
amplification remains excluded (566–575).

Transfer: preserve fresh nominal/effect identity and internal/external
ownership; reusable typed data still needs a proved path, binder, body and
operation translation. Do not infer complete inference or current intrusion
soundness from this successful bounded compiler optimization.

## 6. RCPF-E attribution and event-local ordering correction

Source: `2026-08-05-rcpf-e-clause-link-attribution-and-ordering-addendum.md`.

User approval is explicit August 5 (5, 313–315), authorizing E2a–E2e slices,
not a whole RCPF theorem. It supplements main RCPF §11 after 23 new failures
collapsed to two mechanisms (49–62).

First: root canonicalization erases the original source category, and
ReplayEvidence and canonical replay parents share ReplayConjunction shape.
Therefore read-time kind/shape reconstruction cannot recover attribution
(64–101). Writer boundary partitions replay-origin attribution from retained
Original/Structural/Reduction/Evidence attribution. Factored queries use
their union; legacy all-source attribution is the equality reference
(103–149). Exact link identity is unchanged.

Second: publication fences delay output, not the input read that computes it.
A1 preflight must read the stable pre-event authority view; after-evaluation
waits until Phase B commits the factored state (§3). Phase A legacy mutation
remains unconditional even on failed Factored A1; failed attempts discard
their output and historically retry with fresh LegacyRollback authority.
That retry prescription is an old construction contract, not a current
general recovery requirement.

The text clarifies RCPF's reachable-state equivalence as complete event
boundaries and every consumer-visible view, rather than instruction-by-
instruction transitional states (242–250). This is an explicit interpretation
record requiring original-premise accounting, not a universal theorem here.
Five-source matrix and legacy union parity are required executable gates.

Transfer: retain source attribution at its owner before canonicalization and
distinguish event preparation from publication. Prove the current admission
and consumer boundary. No amount of equality with the old ledger proves its
source rules.

## 7. CPK separation: a semantic service, not passive diagnostics

Source: `2026-08-05-constraint-proof-kernel-separation-plan.md`.

The ADD was a draft; `70ea51ac158dd60be5f15043228bcdeb0d92c1f6` records
explicit approval as-is and changes status/permission to start CPK-0. Scope
is the proof/provenance layer, preserving subtype/worklist/row/SCC/
generalization algorithms (15–20, 43–51, 958–959).

Causal correction: RCPF-E closure covered four named consumers, but five
unconditional flat-parent readers remained. Attempting bound-vs-carrier
classification exposed disagreement between already-approved RCPF-D §3 and
the pinned `cdm_a_9_4_independent_then_claimed_keeps_both_occurrences`
behavior (24–41). This file supplies that later corrective report; it does
not independently reread or settle the pending RCPF-D body.

Defines Semantic Kernel ownership and one canonical ProofOccurrenceStore,
typed semantic foreign keys, occurrence causes, five lineages and projection
OR/AND formula (§§6–8). Prepare/commit retains exact pre-event parents and
distinguishes semantic work, metadata and exact no-op (§9). Two synchronous
queries—replay routing and projection—are semantic services: routing affects
work admission, projection affects exported schemes (§5.2). Invalidation and
attempt failure also cross the layer boundary. Proof storage therefore
cannot be treated as wholly passive diagnostics.

Twenty invariants (§15), thirteen stop-condition bullets (§16), staged
CPK-0–9 migration (§13), and output/proof/performance gates are normative
contracts. No full soundness, principality or unbounded termination proof is
provided. Terminology such as "parity proof" refers here to migration evidence
requirements. The plan requires resolving an inconsistent legacy oracle
before using it (§13 CPK-0, 617–628; §19).

Transfer: reuse single ownership, exact retained premises and explicit
semantic query seams where justified. Current Simple-sub proof obligations
need an actual generation/propagation/generalization correspondence; rebuilding
the historical CPK is not an automatic prerequisite. October 11's abnormal
policy supersedes blanket restoration/retry requirements where unnecessary.

## 8. CPK projection decision: preserve the complete payload

Source: `2026-08-06-cpk-projection-decision-addendum.md`.

Approval: explicit August 6 for CPK-6 Gap 1 API/oracle/failure contract;
consumer cutover still requires separate Slice A/B completion (5–17,
30–33, 971–978). Recorded independent fact-check corrected one Incomplete
classification contradiction; this is historical review provenance, not this
producer's independent certification.

Defines `ProjectionClaimSupport { coverage_root, representative_claim }`,
all-support payload and Unclaimed/Excluded/Included decisions (§§3–5).
Included returns every currently qualifying support, not a first/minimal
winning branch. Claimed and independent identities, ordering and exact
carrier payload remain distinct. Outer evidence/ordinary lower insertion
order must not be replaced by support order.

`Included(empty)` is valid when the formula holds through routes without
directly qualifying payload. It must not become Unclaimed, Excluded or a
fabricated raw Bound parent (§4.4). Non-empty selected-parent assertions were
an implementation tension, not a signed invariant.

Important two-way distinction (§6.2): an existing typed
`ProjectionProofCarrier::Incomplete` is a real independent support with
stored mandatory formula/premises; only underlying optional replay detail
is absent. Missing mandatory carrier/formula/root/premise is a failure and
cannot be converted into that marker. The query supersedes legacy missing-
metadata fail-open (§6.3, 597–599; §11.4).

Round scope fixes one machine, semantic/proof/coverage snapshot, authority
and consumer traversal. Cycle cuts permanently disable further memo sharing
in that round, without truncating support payload (§7). Typed preflight
failure prevents partial publication; historical whole-attempt clean retry
is expressly distinct from local fallback.

Proof status: thirty contractual invariants and twenty stop conditions;
required full-payload shadow parity, not a complete inference theorem. Earlier
boolean-only parity does not certify parent payload (103–105). Reuse identity,
optional/mandatory separation and snapshot requirements only after current
source/consumer premises are proved. Public projected principality is not
established by this lower-filter API.

## 9. CPK routing and its later endpoint correction

Sources: `2026-08-06-cpk-replay-routing-decision-addendum.md` and
`2026-08-06-cpk-7-route-endpoint-decoupling-addendum.md`.

Routing approval is explicitly a recoverable checkpoint August 6, based on
trust in the design route rather than individual scrutiny of every decision
(5–22). Scope excludes CPK-8 removal and CPK-9 closeout. Endpoint correction
has separate explicit approval/review August 6 and supersedes routing
§§2.1,3.2,3.3,5,9; cross-references in §11.1/invariant 20 use its revised
generic-coverage meaning (endpoint correction 16–23, 263–267, 371–373).

Routing defines exact prepared parent side/root/representative/lineage,
pair work, incremental work and Generic/IncrementalOnly/Skip summary.
Parent order is canonical; semantic frontier and first-seen route order are
preserved. Valid no claim differs from missing mirror. The store expressly
cannot detect a completely omitted writer using its own absence alone;
writer coverage and a strengthened legacy comparison are prerequisites
(routing §5.1, 509–529).

Index/complexity contract: local O(Cu+Cl+Ru) plus returned payload and
indexed O(1)/O(log N), no per-pair global scans, full sorts or unnecessary
parent cloning (§7). Natural-event batch preflight precedes all replay
actions; mandatory failure terminates the attempt. The old CPK-5 oracle
skipped mirror mismatches and compared insufficient parent identities;
§9 explicitly rejects it as a cutover gate.

The smallest documentary endpoint falsifier is a two-stage ordinary row-
reduction event: first lower creates reduced upper/live claim; second lower
creates matched route/materialization and moves the claim. The query wrongly
required semantic replay endpoint = current record endpoint (endpoint
correction §1, 41–84). The legitimate constructors are:

```text
unmatched: upper = current reduced endpoint; upper_record = that record
matched:   upper = original row endpoint; upper_record = materialization record
```

Therefore the corrected coverage predicate is

```text
generic_covers(route, query_upper) =
  current_record_endpoint(query_upper) == route.upper
  AND current_record_requires_generic_replay(query_upper)
```

Generic pair work may coexist with residual incremental work whose endpoint
differs. `IncrementalUpperMismatch` means only wrong upper record grouping;
endpoint inequality is not corruption (§2.1–5). The old adapter's rule
"Generic means erase all incremental routes" is withdrawn. The corrected
oracle must preserve exact residual action identity and order. Arbitrary
endpoint corruption detection is not added: the premise is the trusted typed
natural-event constructor; other producers would require a separate validity
design (210–214; stop condition 1).

Proof status: approved API/ordering/failure/performance contracts and a
documented constructor counterexample; no universal source theorem. Both
old and new migration plans share underlying solver/admission assumptions.
Correction of their correspondence is not an independent proof of those
source rules. Current transfer must preserve semantic endpoint versus proof
record ownership whenever that distinction actually exists; do not reconstruct
one from the other or equate this graph with Value-reference intrusion SCCs.

## 10. Dependency graph, transfer and remaining work

```text
source relation ownership + typed propagation
  -> CPROV exact forward derivations -> quiescent OCAST eligibility

MPC conjunction + DPN premise sorts + cycle rules
  -> snapshot/view evaluation round + natural-event batch
  -> RCPF-E writer attribution and stable preflight
  -> CPK single-store separation
     [requires resolving RCPF-D rule contradiction and complete writer coverage]
  -> projection decision/payload preflight
  -> routing exact parents + indexes + strengthened oracle
  -> endpoint/record decoupling correction
  -> separate authority cutover/removal/closeout gates

finalized template + nominal namespace ownership + legacy-generated bundle
  -> M1 typed instance translation -> bounded parity/performance evidence
```

The arrows summarize documented dependencies, not new mathematical
implications. Pending RCPF/RCPF-D/CPK-0 bodies must be read before declaring
their premises reconciled. Later CPK-8 cycle/removal and CPK-SV structural
validity addenda are outside this read lease; the existing hygiene report
already flags their separate corrective scopes. This checkpoint does not
claim the earlier decisions remained the final Oracle contract everywhere.

Transfer classes:

- Reusable after proved translation: exact typed ownership, source-boundary
  relation evidence, alternate derivations without duplicate semantic work,
  snapshot-local memo, exact payload and event publication boundaries.
- Requires correction: all-root memo after a cut, read-time attribution
  reconstruction, boolean-only/mismatch-skipping migration oracle, endpoint-
  record equality and Generic-implies-empty-incremental normalization.
- New current obligations: actual Simple-sub source generation, retained
  residual/attachment lineage, complete Call, generalization/instantiation,
  public projection, soundness/principality, and Value-reference association.
- Historical implementation contract only: old whole-attempt retry/backend,
  specific CPK ledgers and M1 artifact machinery. Retirement needs an actual
  owner/consumer/replacement argument; historical success is not closure.

Recommended next action: read the three pending full bodies, starting with
CPK-0's resolution of the RCPF-D contradiction, then reconcile their exact
supersession chain before updating aggregate coverage or active transfer edges.

## 11. Verification and frozen handoff

Commands used: `git ls-tree -l BASELINE -- <exact paths>`; pinned `git show`
piped to `nl -ba` and consecutive `sed` ranges; line counts; per-path `git log`
including exact ADD and all-ref later history; narrow document-only revision
diffs; bounded searches in the existing core reports. No raw compiler code
was inspected. Historical commands/measurements above were read, not rerun.

Resource use: lightweight sequential Git/text processes; no build, test,
probe, sampling campaign or parallel heavyweight process. Aggregate CPU/RAM
and exact worker wall time were not measured. This is the first coherent
coverage checkpoint, with remaining bodies explicitly pending because of
packet/context volume. It is not completion of the eleven-document assignment.

Checks: all eleven source locators/blob identities and line totals resolve;
eight complete text reads are covered without gaps. This artifact has no
independent review. The author stops writing before handing it to frozen review.

Commit packet:

- Exact write lease: `notes/theory/oracle-inference-document-audit/appendix-batch-b.md`.
- Baseline SHA: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; source blobs are pinned in §1.
- Claim/review status: unreviewed historical coverage/contract audit;
  conditional premises and documentary witnesses, no theorem closure.
- Checks already run: pinned reads, blob/line identity, ADD/revision/deletion
  history and narrow corrective document diffs; zero builds/tests/probes.
- Proposed checkpoint message: `docs(research): audit eight Oracle provenance and CPK appendices`.
- Shared deltas intentionally left for primary/curator: catalogue READ fields
  for eight blobs only; three pending rows; scoped approvals; cycle memo,
  missing metadata, attribution and endpoint supersession edges; current
  transfer ledger and aggregate coverage. No shared record was edited.

## 12. Completion addendum B-v2 — 2026-10-12

Status: unreviewed historical document audit; all eleven assigned pinned texts READ
Method: complete pinned text reading plus document-only corrective revision diffs
Baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, unchanged
Previous checkpoint: Y3 `f4cfc0585`, SHA256
`3081757d417f0d64fb76738353c06c8fc861a3474da30ac54bd1c900f69faa34`

The previous checkpoint's first 26,659 bytes, including §§1–11, are preserved
verbatim. Its pending-coverage statements describe that earlier checkpoint.
This dated addendum supplies the subsequent completion evidence; it does not
rewrite those statements, promote any theorem or certify historical code.

### 12.1 Completed source reads and history

| Pinned source under `notes/design/` | Declared date | Blob | Additional full read |
| --- | --- | --- | --- |
| `2026-08-02-replay-claim-parent-factorization.md` | 2026-08-02 | `4861ae800c62ffbd21e3675e6eed00a177c0740a` | 1–2106 |
| `2026-08-03-rcpf-d-materialization-projection-addendum.md` | 2026-08-03 | `c0ad9b2f271347d54d3d96ae9829202277eab14d` | 1–1326 |
| `2026-08-05-cpk-0-projection-admission-addendum.md` | 2026-08-05 | `4800e3f19687d397a2a4edbcf50c705776272337` | 1–1591 |

Every line was read in consecutive chunks with sufficient output budgets and
no truncation. This adds 5,023 lines to the earlier 6,060, completing 11,083
lines across eleven unique blobs. These three now have complete declared-date
and body coverage. Exact ADD timestamps/commits remain as recorded in §2.

The complete document-only diffs of all eight non-ADD revisions were read:

- RCPF: `7594f331d2498821567d42cddd4c90f397bbe9e9` (August 2,
  153 insertions/32 deletions); `269a84c663d78341daed4e80b39d319614eca4cb`
  (August 5, 14/1); `bece729738b952ac7a2c1a83462ab1b7c27f0df1`
  (August 5, 17/0).
- RCPF-D: `87afed201a46e999878fd69b17c6cdd33e576f38` (August 3,
  178/1); `77faba6dae94295cff7eaa0272c37440af36abf1` (August 3,
  88/1); `59650fd4ac8be955e2f711e254d4b0e8457ddbcc` (August 3,
  219/4); `aac375da27020b7644c784f20ba508c9af30a773` (August 3,
  192/3); `c1df9f39647156bb16c848783e2ad03b5b7d9138` (August 4,
  101/0).
- CPK-0 has no non-ADD in-baseline revision. Its ADD message and complete
  pinned body record the approval and supersession directly.

All-ref `--follow --name-status` histories show exact ADD/MODIFY/DELETE
lineage and no rename for these three paths. All were deleted at the August
18 clean-slate commit `9f03827ff`; no later path-specific correction appears
in the inspected history. Later differently named CPK addenda remain distinct
dependencies and are not excluded by that path-history result.

### 12.2 RCPF: lossless relation factorization and conditional consumer premises

RCPF declares user approval (lines 3–7 and 2104–2106); exact ADD is August 2
11:34:10 JST. The document supplies no separate direct approval receipt/date
beyond this dated approval record and approval-labelled landing message.

Its exact relation is

```text
(result, canonical coverage root, parent side, exact carrier)
    -> first accepted representative claim
```

An occurrence is `(result, carrier)`, where carrier retains pivot, lower,
upper and rule (§4, 410–515). Each side references an immutable finite map
`coverage_root -> representative_claim`; side is retained by attachment,
not duplicated in parent-set identity (§6.3–5). Original admission order
chooses each winner before canonicalization. Later iterators must not
reconstruct that choice. Exact root/side/carrier identity differs from
clause-link identity, which intentionally deduplicates the same root arriving
through both sides (§4.5).

The August 2 revision `7594f331d…` removes first-admission permutation from
persistent parent-set identity, preserving selected representatives and first
witnesses. Its measured motivation is precise: order-bearing sets used
15.52% of logical replay entries, failing the <10% gate; order-free
representative maps used 8.27%, and total membership/map entries were
4,648,988. Global default plus carrier override used 12.05% with 95.37%
overrides, so it was rejected (§2.6, 207–231). These are recorded workload
measurements, not universal compression guarantees.

The physical target is `O(Cq + S + A + RR + BR + clauses + dependency edges)`
while the logical exact relation remains intact (§5). Distinct parent sets
can prevent sharing, and O(L·U) carrier generation remains. The document's
all-pair lower-bound discussion does not prove that every inferencer must
physically allocate one heap object per implication (531–585). No complete
algorithmic lower-bound or source-termination proof appears.

Twenty-three invariants (§10) and sixteen stop conditions (§11.1) specify
required migration behavior. In particular: occurrence-new/root-old is
distinct from new claimed support; no-op causes no allocation/evaluation/
publication; storage sharing is not an atomic event boundary; current live
endpoints cannot reconstruct event-time parent selection. The old missing-
factored-metadata projectable fallback (§8.5, 1249) must be read with the
later quarantine/CPK mandatory-failure rules, already identified in §§6–9
of this report.

Approval versus proof status: the text gives a design model, cost model,
required equalities and executable oracles. It has no named complete
soundness/principality theorem and no proof deriving the selected source
rules. Equality against a legacy ledger establishes representation parity
only under that ledger's correct and complete construction/consumer premises.

The August 5 E closure (`269a84c66…`, 1730–1743) covers the four named
consumer bullets and reports known-failure-only scoped verification. Its
quantitative performance and F soak gates remained uncompleted. The later
same-day F attempt (`bece72973…`, 1745–1760) finds five unconditional flat
readers outside that closure. The complete commit message records explicit
user risk acceptance for a branch-isolated attempt skipping the soak gate;
this is historical permission for that attempt, not proof that the gate
passed. No physical removal was performed. CPK's subsequent rebuild route
replaces the attempted construction-specific migration, preserving the
genuine semantic and performance requirements.

### 12.3 RCPF-D: scoped approval, retained winners and changed observable order

RCPF-D declares August 3 **blanket advance approval**, explicitly distinct
from individual content review. Lines 9–21 quote the 10:28 JST authorization
to work until 17:00 and explain its scope/provenance. The later §11 and §12
ordering changes have separate explicit user decisions, recorded in their
bodies and full revision messages. Do not infer that the original blanket
approval alone supplied those later decisions.

Initial construction (§§2–4): add a result-local root index without copying
witness authority; return exact same-event accepted deltas; process Phase A
unconditional legacy mutation, Phase B factored commit/health, then Phase C
derived mutation and complete-state publication. A publication fence cannot
make incomplete evaluator input safe. This is an operational transaction
contract; historical whole-attempt discard/retry is not a general current
Simple-sub recovery mandate.

The correction chain is sequential and substantive:

1. §9 / `87afed201…`: splitting Replay and NonReplay stores discarded
   which kind won the same root. Retain `FirstQualifiedParentSource` at the
   common writer; neither replay priority nor later iterator reconstruction
   establishes the selected first winner.
2. §10 / `77faba6da…`: two histories,
   `NonReplay(root_b); Replay(root_a)` and the reverse, have identical
   retained root/winner maps but different legacy proof-vector order
   (741–760). That order reaches generalized parents, truncated explanation,
   portable IDs and duplicate-span survivors (762–805). Thus root/winner
   equality alone is insufficient consumer evidence.
3. §11 / `59650fd4a…`: user-approved lower ordering uses claimed roots
   ascending, then independent carriers under a complete explicit comparator.
   It changes already-shipped legacy diagnostic behavior independently of
   RCPF authority cutover, potentially changing primary spans and truncation
   survivors (819–986). A proposed four-event oracle covers all 24
   permutations and the 256-edge witness cap. These finite checks do not
   prove arbitrary source-order independence.
4. §12 / `aac375da2…`: a two-root target-late fixture exposes historical
   upper claim order to later replay under both authorities. Equality between
   legacy and factored behavior therefore does not establish the stronger
   intended invariance (1039–1081). Canonical root ordering is introduced at
   all three upper claim writers, with same-root winners and source admission
   evidence retained. The text records explicit user approval after the FAIL.
5. §13 / `c1df9f396…`: reports landed slices and migration-correctness
   checks, including claim-move index repair and one end-to-end quarantine
   retry comparison. Its discarded D4-3 attempt confused a logical equality
   map with a lossless mutation plan, causing 21 failures (1261–1276).

The final body says D migration is correctness-complete but performance-
incomplete. Its one warm-release full-std observation reports
`std::text::parse` 53.239 seconds, 9.31% worse than 48.705 seconds, missing
15-second intermediate and 0.5-second product targets (§13.3). It explicitly
says the F soak matrix is broader than the single retry comparison and one
timing observation (§13.4). Historical completion must remain scoped to
these reported gates; later flat-reader discovery and classifier supersession
prevent treating it as complete source soundness or total dependency removal.

The RCPF diagnostic-isolation premise in main §10 invariant 23 is consequently
conditional: a separate explanation traversal does not guarantee unchanged
output when its incoming generalized-parent sequence changes. The later D
text exposes that indirect dependency and records authorized canonicalization.
This audit preserves the original claim and its later repaired premise rather
than treating the original separation assertion as an unconditional theorem.

### 12.4 CPK-0: exact supersession of the Bound/Carrier classifier

CPK-0 declares August 5 explicit approval (5, 1586–1591), confirmed by exact
ADD `89a6de2289079c42a85d788fefa98ad19c50d5d1`, 20:57:21 JST. Scope is
design plus test-only CPK-0a/b/c baseline preparation; it does not authorize
production behavior change or immediate CPK-1 cutover (23–37, §12).

It supersedes **only** D §3's rule (CPK-0 §3.1, 628–648):

```text
new roots nonempty && lower previously had no claimed roots -> Bound(producer)
otherwise                                                -> Carrier(event)
```

The later document classifies this as an **incomplete model**, not simply a
wrong boolean. It conflates new claimed roots with the producer's first
qualified-parent batch and cannot represent necessary independent-support
bootstrap (CPK-0 §1.2 and §3).

The replacement retains four independent facts: producer-qualified membership
before the event, ledger existence before the event, new roots, and exact
event carrier. `ProjectionAdmissionPlan` has separate claimed-root and
independent-support plans (§3.2–4, 650–755):

- no target or exact no-op: no work;
- ledger absent and no roots after event: create no ledger;
- ledger absent and roots present: full root bootstrap plus full bound-record
  derivation bootstrap;
- ledger present and first newly inserted qualified-parent batch: root delta
  if any, plus producer full scan;
- later ordinary event: root delta plus exact event-carrier work;
- record bootstrap subsumes an overlapping producer scan.

The smallest documented discriminator (§4.2, 795–819) has a pre-existing
direct claimed root/ledger, a producer with no qualified parent, and its
first replay arriving with that same root. New-root delta is empty, yet
producer full scan is required. Therefore a test of new roots cannot replace
the first-qualified-batch signal. Independently, §4.1 preserves a prior
independent bound derivation when the first claimed arrival creates the
ledger. These are document-contract witnesses, not new source-program
counterexamples or executed compiler findings.

Other D rules remain explicitly retained: Phase A/B/C order, complete
pre-event view, same-root first winner, canonical lower and upper order,
diagnostic isolation, attempt authority and failed-output nonpublication
(641–648). CPK-0 further requires ordered action vectors with all lookups/
allocations preflighted; an unordered root/lineage map is not a mutation plan
(§§5–7).

Inventory expansion (§2.4): four additional flat dependencies directly block
RCPF-F—structural-root propagation, target-late clause bootstrap, reduction
exact dedup, independent/qualified carrier classification. Two more require
CPK cutover but are not themselves replay-parent removal blockers—flat clause
ID mapping and independent expanded-link reads. Of the original five readers,
dependency-chain propagation was already dispatched at `2b810745`; the
remaining four had unresolved semantics. This distinguishes scoped E
completion from a complete producer/consumer inventory.

Two reference surfaces are defined (§8): `SemanticExecutionSnapshot`
preserves actual queue/frontier/replay/publication/SCC/output order;
`LogicalProofSnapshot` canonicalizes relation/graph identity while preserving
consumer-visible provenance and truncation. Raw flat Vec length, Bound/Carrier
tags, known inconsistent legacy state and partial helper fixtures are
explicitly forbidden oracles (1314–1327). This repairs the premise of the
legacy comparison; it does not independently prove the selected source rules.

Proof status: thirty operational invariants and twenty-three stop conditions,
four fixture-directed plan explanations and a required future baseline matrix.
No general inference theorem is proved. CPK-0's "resolved" entries are scoped
design decisions, distinct from implementation completeness or mathematical
closure.

### 12.5 Transfer, checks and frozen completion packet

The repaired historical dependency chain is:

```text
exact carrier + event-time parents + direct first-winner capture
  -> RCPF immutable finite-map representation
  -> D result-local deltas and event-complete publication
  -> cross-kind winner retention
  -> authorized lower/upper consumer ordering
  -> later inventory and Bound/Carrier insufficiency discovery
  -> CPK-0 independent claimed/independent admission plans
  -> separately specified CPK projection/routing consumers and removal gates
```

Current transfer remains conditional on authentic source constructors and
consumers: preserve ownership, scope, lineage, exact admitted action and
required correlated evidence at construction; prove any generalization/export
projection preserves the original solution and observation requirements.
Canonical numeric ordering is not a causal rank, a runtime identity theorem
or the current Value-reference SCC qualification condition. Historical proof
ledger equalities do not establish native Simple-sub soundness, principality,
Complete Call or parent/copy type equality. Conversely, current retirement
does not require reconstructing every obsolete ledger before proving those
genuine obligations; identify actual consumers and retained certificates.

Verification: initial local and `f4cfc0585` report hashes both matched the
expected checkpoint; all three pinned blobs, declared dates and line totals
resolved; full non-ADD document diffs and approval messages were read; exact
ADD and all-ref follow/deletion histories were inspected. After appending,
the original 26,659-byte prefix is checked against its original SHA256.
No source code inspection, tests, builds, runtime probes, performance samples
or Git mutations occurred. Historical measurements and test outcomes are
reported as read, not rerun. Sequential lightweight text/Git processes were
used; aggregate CPU/RAM and exact wall time remain unmeasured.

Unverified scope: underlying implementation/test artifacts, full source laws,
general correctness of the legacy oracles, every external dependency, later
differently named CPK-8/CPK-SV corrective bodies and current production
correspondence. No unread body remains inside this exact eleven-document
lease. Full reading is not proof closure or fresh independent review.

Recommended next action: primary/curator records the three additional READ
rows and the exact scoped supersession edges, then subjects the coherent
document audit to its assigned independent review before any status promotion.

Commit packet B-v2:

- Exact write lease: `notes/theory/oracle-inference-document-audit/appendix-batch-b.md`.
- Frozen historical baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`;
  report dependency checkpoint: Y3 `f4cfc0585`.
- Changed dependency hashes: none; the three source blobs are pinned in §12.1.
- Changed output: append-only dated B-v2 addendum; §§1–11 preserved verbatim.
- Claim/review status: complete leased reading, unreviewed historical audit;
  operational/conditional evidence, no theorem closure.
- Checks already run: full reads, blob/line identity, full corrective
  document diffs, approval/ADD/follow/deletion history and preserved-prefix
  integrity; zero tests/builds/probes.
- Proposed checkpoint message: `docs(research): complete Oracle RCPF and CPK-0 appendix reads`.
- Shared deltas deferred to primary/curator: three READ rows, all-eleven
  coverage totals, D §3-only supersession, indirect diagnostic-order premise,
  scoped migration-completion/performance status and current transfer edges.
  No shared task/index/catalogue was edited. Writing stops for frozen handoff.
