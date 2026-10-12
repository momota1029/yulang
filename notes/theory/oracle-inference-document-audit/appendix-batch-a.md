# Oracle document audit: appendix batch A

Date: 2026-10-12
Status: frozen producer documentary audit; independent review pending; no theorem closure
Anchor: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Scope: eleven specifically leased historical documents, their recorded claims,
approval scope and path history. No compiler inspection, builds, tests, probes,
production edits or semantic adoption.

## 1. Corpus and method

Ten documents were read completely from the anchor's Git blobs, using contiguous
numbered chunks of at most 373 lines. They contain 9,914 lines / 536,180 bytes.
The June flow plan is absent from the anchor and has no path history reachable
from that anchor. The primary separately authorized its rescue version at
`5b7897bbc35573b3d496aab9d621647940e21894`: 554 lines / 15,784 bytes.
Total full-body coverage is 10,468 lines / 551,964 bytes, in 33 bounded reads.
No assigned body output was truncated. Earlier summaries were consulted only to
locate accepted findings and existing DAG names; full-body coverage here does
not repeat the existing Boolean witness, allocation-rank derivation or TeX audit.

Historical source locators below identify what each document says its owners
were. Their compiler files were not inspected. Recorded test results, census,
profiling and implementation completion are documentary evidence, not checks
executed by this worker. The original theorem statements and selected source
meaning remain with their existing proof/source owners.

### Metadata and full reading coverage

All paths in this table are under `notes/design/`.

| ID | File | Full READ range | Recorded status / approval scope |
| --- | --- | --- | --- |
| EF | `2026-06-22-effect-flow-lowering-plan.md` | rescue 1–554 | Unsigned plan, no approval/date header; June 22 dates come from Git. Excluded from the Oracle anchor tree and authority. |
| OD | `2026-07-15-owner-level-dirty-scheduling-spec.md` | anchor 1–1268 | July 15 reference specification approved by user/Claude; each implementation stage separately gated. Header and July 16 closeout record Stages 0–7 implemented, verified, production default. |
| SS | `2026-07-15-suffix-safety-oracle-spec.md` | anchor 1–985 | July 15 reference specification approved, including explicit per-stage authorization requirement; final header says abandoned after Stage 0 falsified the predictive hypothesis. No production oracle activation. |
| OC | `2026-07-21-ordinary-cast-resolution-spec.md` | anchor 1–786 | July 21 user/Claude reference approval only, expressly excluding even OCAST-A implementation authorization. Constructor-pair ambiguity policy already selected. |
| PU | `2026-07-22-parameter-use-site-provenance-spec.md` | anchor 1–1234 | July 22 user/Claude reference approval only, expressly excluding even PUSP-A implementation authorization. Opening draft label is retained. |
| SU | `2026-07-22-subtype-explanation-bridge-spec.md` | anchor 1–1686 | July 22 reference approval only; July 23 user-approved amendments add SUBP-I and restage SUBP-G. Final export-order fix is attributed to Claude; that last paragraph does not itself record explicit user approval. |
| DC | `2026-07-30-derived-row-claim-propagation-gap.md` | anchor 1–1052 | Draft title retained; July 31 user approval explicitly selects §5.1D, §5.4C and the other recommendations, authorizing DCP-A..E. |
| CD | `2026-07-31-claim-parent-delta-materialization.md` | anchor 1–661 | July 31 user-approved design, committed with MPC/DPN on August 1; CDM-0 preflight precedes implementation. |
| MP | `2026-07-31-mixed-proof-conjunctive-ownership.md` | anchor 1–708 | July 31 user-approved addendum to DCP; MPC-0 occurrence audit precedes implementation. |
| DP | `2026-08-01-derived-unary-premise-nodes.md` | anchor 1–733 | August 1 user-approved replacement of specified MPC premise clauses; DPN-0 remains required before implementation. |
| U3 | `2026-08-01-urr-v3-causal-qualification.md` | anchor 1–801 | August 1 approved, implementation held. Opening outcome addendum preserves neutral A, discards evaluator B and closes motivating bug elsewhere. |

Approval and proof validity are separate axes. Reference approval does not turn
proposed staging, universal invariants or future exit conditions into completed
proofs. Historical per-stage permission is not current implementation authority.

### Path and revision history

Read-only `git log <anchor> --follow --name-status` covers all ten anchor paths.
These histories contain additions and modifications, with no recorded rename
or deletion in their anchor ancestry. Listed timestamps are commit author dates
in `+09:00`; they need not equal the document's stated decision date.

| ID | Add / subsequent recorded revisions, oldest first |
| --- | --- |
| EF | Rescue-only: `575a8a4e4` June 22 19:50 add; `5b7897bbc` June 22 22:59 adds Implementation Findings. `--all --follow` exposes those two records; `merge-base --is-ancestor 5b7897bbc <anchor>` returns 1. Anchor absence is not evidence of an identified deletion commit. |
| OD | `71e2225a6` July 15 reference approval/add; `1ede6ac77` failed Stage 2; `53a09268e` corrected Stage 2; `9b5ed806b` July 16 failed Stage 5; `03d2a91ed` corrected Stage 5; `734c3f4da` Stage 6; `1501e96f3` Stage 7; `fb5a42902` July 22 stale-header correction. |
| SS | `7788219c6` July 15 reference approval/add; `fb5a42902` July 22 corrects header to abandoned following July 15 Stage 0 result. The body does not contain a completed Stage 0 experiment report. |
| OC | `15c46d0c7` July 21 draft/add; `7f3513864` July 21 reference approval. |
| PU | `bc9b5f97a` July 22 add, including reference approval. |
| SU | `cc149542f` July 22 add; `dfe748a30` July 23 adds public API threading; `0bd022783` July 23 restages portable traversal; `d837a5937` July 23 export anchor starvation/fix direction. |
| DC | `c49a4faab` July 30 draft/add; `93479f84b` July 31 approval. |
| CD, MP, DP | `51d56605e` August 1 adds the approved chain together. Their decision dates remain those printed in their bodies. |
| U3 | `52a1cf712` August 1 approved add; `8bf3e62f6` August 1 records implementation held and motivating bug closed elsewhere. |

No earlier complete revision body was substituted for a later frozen body.
EF's one modifying diff was inspected: it adds the 37-line findings section,
without establishing closure of the remaining source/fan-out premise.

## 2. Dependency group: lowering, scheduling and cache safety

### EF: source-to-fan-out correspondence, rescue-only

**Definitions/claim.** Lines 16–34 assert that the complete TeX draft proves a
row-only fact machine after effect-sequence fan-out normalization, and identify
administrative effect joins as a Rust/source correspondence gap. Lines 64–80
propose that semantic rows, handler residual tails and function return-effect
slots stay solver variables, while administrative sequencing ports become
`EffectFlowId`. `Empty/Var/Pos/Seq/Hole` and producer/consumer fan-out are defined
at 82–142. The quotient removes a join and emits every producer/consumer composed
edge; this is a proposed construction, not an independently established source
equivalence theorem.

**Exact premises and exclusions.** Preserve `push(Empty)`, exact labels and
monomorphic recursive RHS roots; prohibit pop-count clamps and weight-insensitive
replay no-ops (8–12,52–62,304–327,371–374). Catch residuals must remain semantic
(413–416). The proof requires the actual source contours to satisfy the
fan-out/zero-displacement hypothesis; successful hand-written fan-out does not
supply that premise.

**Recorded failure and status.** Findings 457–492 retain a continuation/row-split
contour with two paths to the defined skeleton output. Removing the public
scrutinee-row constraint loses principal information; returning only residual
effect terminates poorly. Known subtracts versus late callback subtracts need
different transport. Phases 0–7 and success criteria 545–554 are plans. A requested
structural SCC regression over source-generated cycles (516–517) is not a proof
of its universal conclusion. No approval, soundness, principality or Rust
termination closure is recorded.

**Owners/transfer.** `ExprLowerer`, `make_app`, defined-lambda skeleton construction,
`lower_catch_with_scrutinee`, and materialization boundaries. This adds a concrete
historical bridge locator to DW09–DW14: actual administrative/semantic
classification and composition remain OPEN. It does not repair the already
challenged complete-draft algebra or mandate this representation in Simple-sub.

### OD: terminal owner solve scheduling

**Conditional contract.** For each session and owner, reusable outcomes are
`RootUnavailable | NoProgress`; with the same complete dependency frontier,
resolving again returns the same terminal outcome and publishes no semantic
mutation (28–40). §4,197–220 requires unchanged resources actually read, drained
journal, consistent unresolved selections, no unknown/lost/overflowed/version
mutation, and valid session/resource lifetime. Determinism and complete observed
read/mutation coverage are premises; fixture clean rates do not prove them.

**Definitions/invariants.** `SelectionUse.parent` is the owner. Fingerprints include
SCC root, owner roles/selections, constraint bounds/neighbors/subtract facts/current
and birth levels/pre-pop families, transitive candidate buckets, queried taint and
cross-owner selection data, and applied-resolution membership (106–158).
Progress is never cached. Typed journal/reverse subscriptions, exact dependency
replacement, checked generations, deterministic owner order, same-pass draining,
session cleanup and unknown-state full fallback are specified in §5. Budget
failure disables optimization, preserving the ordinary solver (1109–1125).

**Evidence and supersession.** Initial three-fixture shadow observes 21,035 clean
predictions among 21,532 solves; no repeated-root-unavailable evidence (97–104,
160–192). Shadow compares three terminal classes, not all internal statistics.
Stages 2/5 discard unbounded inactive logging, layering errors, and release hooks
left test-gated (660–749,799–881). Final Stage 6 preserves cross-pass recording
but records only subscribed keys; naive pass-only recording had reduced clean
rate to about 3.59% (898–940). This later result supersedes the earlier temporary
activation-window wording. Stage 7 records completion (963–1056); Markdown
end-to-end same-time gain 5.799% differs from 97.78% clean-call rate. Historical
multi-session timing milestones are expressly not one controlled A/B series.

**Owners/transfer.** `drain_work`, `resolve_method_tainted_roles_for_def`,
`MethodTaintIndex`, `ConstraintMachine` read/mutation APIs and session tables.
No new inference theorem closes. Retain the conditional dependency-preserving
optimization pattern only after current writer/read coverage is established;
do not import legacy role search or its scheduling prerequisites wholesale.

### SS: abandoned predictive suffix safety

**Original universal implication.** For prefix P, suffix S, canonical artifact C(P):
`ProvenSafe(C(P),S) => suffix_interface(cold(P+S)) ≡α suffix_interface(warm(C(P),S))`
(13–24). Alpha equality includes sharing/lifetime, residual roles, recursive/stack
binders and visible candidates. Runtime equality is weaker. Closed Q/R/B artifacts
do not establish commutation of attaching to open roots then generalizing versus
generalizing then instantiating (145–186).

**Candidate sufficient route.** Proof-only counterfactual O binders must not become
production B or protected variables (105–121). Complete pre-drain prefix frontier,
resumable shallow suffix views, exact equality/share closure, bijective namespaces,
role readiness/candidate/pending-work parity and six open-use bridge conditions
are specified at 188–493. Unsupported/budget cases compile cold; the intended
congruence theorem is explicitly unproved at 926–930.

**Withdrawal.** Header 5–6 records Stage 0 falsification and abandonment. The
reference-approval footer 983 excludes every stage's implementation permission and
requires revision if characterization falsifies the architecture. The frozen
body preserves proposed later stages, not evidence they ran. Silent successful
warm HTML divergence and valid emptyB are documented counterexamples to
marker-only, successful-warm and runtime-equality shortcuts; no new experiment
was executed here.

**Transfer.** Retain precise cache observation and binder-sharing questions when
relevant. Retire this failed predictive construction as a completed historical
attempt, not as a proved cache congruence theorem. It supplies no source
generalization/principality theorem or present cache implementation authority.

## 3. Dependency group: casts and explanation transport

### OC: constructor-pair cast cardinality

**Selected meaning.** Visible value declarations for the exact source/target
constructor pair classify as 0 → Missing, 1 → Unique(rule), 2+ → Ambiguous; only Unique
contributes constraints/subtype evidence/runtime instances (203–267). Generic
viability, multi-hop search and precedence are excluded, including same-pair
generic declarations with disjoint-looking applicability. This accepted policy
must not be reinterpreted by the audit.

**Required invariant.** Infer working registry and durable poly registry must
represent the same visible declarations; duplicate registration of one declaration
is hygiene, not a language-level second declaration (326–359). Compact discovery
Missing means no ingress; a required nominal boundary Missing means rejection.
All/any/first-match shortcuts fail the explicit consumer table 339–350. The
concrete struct-bool/int and function-result-bool/int witnesses (23–57) depend on
their actual generated required relation; they do not prove a complete annotation
shape relation.

**Status/owners.** Reference-approved staging only. Source locators include
`NominalCastNeeded`, `constrain_nominal_cast`, `find_next_compact_cast`,
`TypeGraph::constrain_direct_cast`, emission lookup and boolean candidate subtype.
Legacy `specialize_roots` coverage remains a separate decision. OCAST-A..H and
exit criteria are proposed checks, not local completed checks. Reuse deterministic
selected-declaration evidence and exact consumer policy; full source soundness,
annotation coverage and successor correspondence remain OPEN.

### PU: same-session parameter provenance

**Definitions/invariants.** Source-owned `BodyRequirement` is distinct from an
OCAST-eligible boundary. Exact contributors survive as generalized scheme
witnesses at typed polarized paths; per-use instantiation edges return to those
shared witnesses. No source span, graph identity or completeness status enters
semanticHash/Eq, admission, generalization, instantiation, cache or termination
(313–409,411–658). Alternate derivations remain separate edges; genuinely joint
transformations use ordered hyperedges. Concrete-finalized parameters must be
covered, not only quantifiers. Imported/cache schemes are explicitly unbridged.

**Documented witness/status.** Original unannotated if-condition parameter query
reaches a bool root through 19 nodes / 18 edges but ends UnknownInternal; call-side
11 nodes / 9 edges stops at the copied scheme (63–98). This locates information loss,
not a typing theorem. PUSP-A..F plans and July 22 reference approval do not
themselves record project completion. SU's later baseline separately reports
PUSP completion at `ff88e762`; that statement does not certify every broader
transformation/path listed in PU's taxonomy.

**Owners/transfer.** Requirement creation, compact collection/simplification,
finalization, `SchemeInstantiator` clone maps, local and SCC/batch instantiation,
canonical child/direct-bound admission, bounded query and presentation. Transfer
construction-time evidence retention and honest incomplete degradation. These
explanatory witnesses do not discharge joint scoped generalization, principality,
let-rec soundness or exact source-to-runtime hygiene.

### SU: portable subtype explanation and discovered reachability gaps

**Definitions/invariants.** Portable immutable shared snapshot plus occurrence
keys `(Definition|Expression|Pattern,role,typed path)`; interned type-node equality
does not establish source ownership (307–347,381–505,507–791). Snapshot/materialized
mapping/work provenance is adjacent to semantic types and queue identity.
Duplicate evidence never requeues semantic work. Completeness cannot improve
after an incomplete mapping. Initial support is cold/same-build; caches install
empty sidecars and preserve the original error.

**Recorded scope and corrections.** Four initial cases, three failure arms, are
distinguished explicitly (66–103). SUBP-F at `9be09b6e` was validated using synthetic
materialized values; its sidecar was dropped at the production entry, so it did
not prove real occurrence reachability (1268–1279). July 23 SUBP-I adds real API,
instantiation and owner-compatible root transport; I-4 container-identity gaps
remain deferred. The July 23 G amendment acknowledges no production infer↔specialize
dependency and no remaining session IDs: it requires a new bounded portable
walker, not a literal call into session-local queries (1382–1473,1680–1682).

**Budget counterexample.** July 23 H-1 amendment 1684 records roughly 14,467 occurrence
roots against global `max_anchors = 64`. Std-first deterministic ordering exhausts the
budget before user roots; passing a std-free unit test therefore did not establish
real CLI coverage. Increasing anchors alone moves pressure to node/edge budgets
and can cost 60+s. Paragraph 1686 selects source-origin-prioritized export, not
unbounded growth. It records a scoped fix direction, without a completed check
or explicit user approval in that paragraph.

**Transfer.** Exact occurrence retention, production reachability and aggregate
budget coverage are separate obligations. No later diagnostic pass proves source
typing soundness, mathematical generalization correctness or full solver
termination. Synthetic infrastructure success must not close an active consumer
gate. Exact historical diagnostic topology is not a general current correctness
requirement under October 11 principles.

## 4. Dependency group: claim propagation and proof composition

The documentary order is URR-H→DC propagation→CD cost recovery/MP clauses→DP
typed premises→root/cycle addendum→U3 attempted qualification. CD and MP are
semantically distinct; MP-B performance is evaluated after CD recovery. Later
GWCB (outside this batch, covered separately) refines diagnostic capture of the
actual decisive clause.

### DC: exact lineage and mixed proof support

**Contract.** Accounting propagates through both exact binary replay sides,
generic structural children and one-sided concrete lower admission, without
creating semantic relations (329–375,379–433,435–615). Physical row-node sharing
does not imply bound/owner sharing. Covered and independent proofs may coexist
on one canonical record; project endpoint once and use only projectable support
for scheme provenance. Last-live-state removal restores projection. New,
canonical/prefilter duplicate, evidence and promotion paths retain exact metadata.

**Status/dependencies.** Header explicitly selects D/C recommendations. §5.1
defers conjunction; additive lineage does not mean each inherited premise is a
complete alternative proof. MP explicitly records firing DC stop condition 2.
Original DC dedup language keyed by carrier kind/root/side is subsequently refined
to exact carrier by `95b95586`, which CD must preserve. DCP-A..E completion criteria
are requirements; MP records A..D landed and E merging into its later closeout,
not a general soundness/principality theorem.

**Owners/transfer.** Replay planning, `enqueue_derived_subtype`, stable lower
admission, claim/support ledgers, shared projection consumers and liveness epoch
publication. Exact source construction and justification that suppressed covered
relations are semantically redundant remain separate from successful metadata
transport. The historical nested motivating witness is later invalidated by U3;
that does not erase independently specified/checked carrier contracts.

### CD: incremental ledger equivalence and cost

**Original quantified invariant.** At every reachable state, delta-maintained
ledger equals bulk recomputed ledger (§3 invariant 2,268–269). Bootstrap once from
existing local derivations, then process every event's exact delta with the same
pre-link classification visibility (176–202). Preserve unconditional
`(result,root,side,exact replay)` registration and distinct independent/claimed
occurrences. Root materialization summary cannot answer carrier qualification.

**Evidence versus theorem.** §1.3 derives possibleO(C²D)/O(C³) rescanning growth;
§1.5 argues feasibility from additive storage. Universal equivalence still needs
complete writer/event coverage and the bootstrap/event induction. The test-only
bulk oracle is the old implementation, sharing classification assumptions;
its initial self-comparison is expressly trivial (558–563). Later differential
agreement supports tested-state equivalence, not independent source semantics.
Measured 6.126s→481.875s regression and targets parse≤15s/five-case≤550s are historical
performance data/gates, not a termination or complexity proof over all inputs.

**Transfer.** Retain exact identities, single owned construction and bounded
delta maintenance where current data has the same proven add-only/event model.
Do not assume current mutable indexes are append-only, or import bulk equality
as proof of cast, effect or typing soundness. CDM-0..E are staged obligations in
this file; DP separately reports CDM landed at its baseline `cc53f749`.

### MP: alternatives versus joint replay proof

**Exact proposed characterization.** A record is projected iff it has a complete
proof using only projectable leaves (256–257). Record clauses are OR;
ReplayConjunction consumes exact lower AND upper; standalone support is a complete
alternative; derived unary delegates to its premise. Attribution belongs to the
link occurrence, not the claim's lineage kind (172–264). No claim cross product
or proof-path enumeration. Metadata absence falls toward preserving projection,
but confirmed paths needing fallback stop implementation.

**Premises/status.** The characterization assumes the ledger completely and
correctly represents actual complete proofs and that covered information is
already represented by the live reduction route (259–263). It is not established
by the Boolean rule definition. Existing five controls concern real independent
alternatives; MPC-0 must first rule out standalone alternatives at the motivating
record (507–531). The previous audit already derives the minimized conditional
AND-vs-OR witness; no new duplicate proof/probe is offered here.

**Supersession/reading cautions.** MP's bound-only DerivedUnary premise and
Standalone fallback (210–213) are withdrawn by DP. D3 says circular clause reentry
is false with other alternatives continuing (246–248), while D4's blanket cycle
phrase lists projectable fallback (276–277); do not treat that retained phrase
as an independently proved universal cycle policy. Existing later cycle authority
and its audited scope govern the selected operational rule. Neither memoization
nor a finite guarded traversal proves all cyclic proof meanings or whole solver
termination.

### DP: typed premise ownership, then a withdrawn rank premise

**Replacement.** Ordinary lower-record map misses are structural, not temporary:
upper-only/row-decomposing constraints have no lower record (79–115). Therefore
premises become `Record|Constraint|RootCoverage` at 169–198, with carrier-held IDs,
record AND replay, constraint OR over linked record/routes/root, and liveness leaf
evaluation (200–251). Registration-time lookup/fallback, MP's premise key and
its resolution stop condition are replaced only in the scopes enumerated 529–545.

**Required conditions.** Every confirmed constraint premise has at least one
evidence source; dependency chain wiring covers late map/route and liveness
changes; normalized root identity remains valid; storage is bounded by link
events times the structural chain measure (267–347,557–585). Census of a finite
workload does not prove a uniform depth bound or all-source event completeness.

**Withdrawal already adjudicated elsewhere.** DP asserts structural parents
precede children and constraint-only recursion is well-founded (235–239,
335–341). The existing reviewed effect-history audit records the same-day
root/cycle addendum's 88 rank violations and withdrawal of allocation-order rank.
This batch does not redo that derivation or read that separately owned addendum.
Keep the originalDP assertion historical, not an established termination lemma.
Retain typed construction premises and the later actual guard contract with
their own proof obligations.

### U3: approved but unused evaluator refinement

**Candidate predicate.** `ActiveCausalQualification(D,P,R)` requires DirectOriginal,
exact producer-local parent route, Reduced root, current record co-location and
live root (154–203). Candidate index is append-only, but live/co-location are
rechecked; multiple active routes OR and replay's premises AND. Qualification does
not rewrite the claim coverage root or affect generic replay (315–390).
Movement/liveness publication owners are explicitly unverified before U3-0
(261–313); linear walk/invalidation claims depend on those premises.

**Controlling outcome.** Opening 7–28 supersedes the later retained motivating-gap
and deployment prose: A neutral registration landed `c4490082`; D1 evaluator
overmatches the independent mixed-record control; D1' requires a route absent
at the actual producer. B was discarded uncommitted. The motivating nested
hand-built callback violates LVB v5's deferred concrete-ref rule; correcting only
that construction closes it at `a65655b2`, without claim propagation changes.
Future reconsideration requires an authentic exact-route case and review;
the retired motivating fixture supplies no such premise.

**Transfer.** Record evaluatorB as unnecessary/discarded for that motivation,
not proved, and do not leave repair of that witness as an active Simple-sub
prerequisite. NeutralA is not proof of refinement correctness. Genuine effect
hygiene/soundness/principality/source correspondence remain OPEN elsewhere.

## 5. Proposed DAG and current-transfer deltas

These are proposals for the primary/curator, not changes to shared records.

| Delta | Evidence class and exact retained premise | Current consequence |
| --- | --- | --- |
| Add EF rescue pointer to DW09–DW14 source/fan-out seam | Explicit unfinished implementation correspondence; no anchor authority | Actual source effect construction, zero-cycle displacement and generated label composition remain OPEN. Do not relabel full draft proved. |
| Distinguish OD optimization theorem from fixture closeout | Conditional unchanged-complete-read-frontier contract; production/test/measurement history | Current optimization must establish its own complete writes/reads and replay/publication invariants. No global termination closure. |
| Retire SS proposed predictive route | Stage 0-abandoned status; sufficient commutation criterion/formal congruence unproved | Keep genuine supported cache semantic equivalence if required; no obligation to rehabilitate this predictor. |
| Keep OC selected meaning separate from registry proof | Approved pair-cardinality semantics; registry parity/generation/consumer contracts | No reinterpretation of ambiguity policy; source constraints and actual consumer correspondence still required. |
| Split PU/SU observational theorem from source generalization theorem | Exact contributor/occurrence capture and bounded explanation coverage | Typing DAG's joint generalization, correlated instantiation, let-rec and principality gates remain OPEN. |
| Split SU infrastructure from active production reachability | SyntheticF, realI, portableG and std-scaleH starvation are separate gates | A passing synthetic query cannot certify current semantic or consumer reachability. Aggregate budgets require real supported inputs. |
| DC→MP separates lineage accounting from complete proof composition | Exact transported carriers do not turn AND premises into OR alternatives | Source proof incidence and semantics of covered relation suppression remain OPEN. |
| CD equivalence is conditional on complete event ownership | Bulk oracle shares old classification/source assumptions | An independent specification argument is needed before claiming semantic preservation for a successor. |
| MP→DP replaces missing premise reconstruction with typed construction evidence | Map's population excludes upper-only constraints | Prefer evidence at source owners; do not require reconstructing nonexistent records. |
| DP allocation rank remains withdrawn | Existing reviewed same-day correction | No allocation-ID termination proof or automatic cyclic evaluator theorem. |
| U3-B motivating dependency retired | Explicit overmatch, absent route and invalid-source-witness correction | No third equivalent qualification probe; preserve authentic hygiene and source gates. |

Current October 10 withdrawal preserves genuine complete Call, effect hygiene,
soundness and principality while retiring replaced legacy prerequisites only
with mechanism-specific evidence. October 11 inference principles select normal
Simple-sub generation/accumulation/propagation/levels/extrusion/intrusion/
generalization and necessary private-attempt publication safety. These policies
do not prove the transfer premises. In particular, historical row/proof/SCC IDs
are not the actual-value/reference/type-occurrence association needed by current
intrusion; explanation sidecars are not semantic source certificates merely
because their constructors retain exact historical record IDs.

No theorem in the existing integrated DAG is promoted by this appendix. The
already reviewed conditional Boolean/rank results remain at their exact scope.
No current code behavior, current specification gap, new language restriction,
restated toy probe or experimental success was used to fill a missing premise.

## 6. Reproducibility, independence and frozen hashes

Commands: read-only `git show <revision>:<path> | nl -ba | sed -n '<range>p'`,
`git log <anchor> --follow --format=... --name-status -- <path>`, rescue-only
`git log --all --follow`, `git merge-base --is-ancestor`, `git rev-parse`, and
Python `subprocess`/`hashlib` over immutable blob bytes. Targeted reads of existing
auditREADME/typing/hygiene reports locate accepted DAG/status information.
No tests, builds, probes, measurements, Git mutations or child delegation.
Process concurrency: 1. CPU/RSS and total reasoning wall time were not measured;
body reads/history/hash commands were small, with no heavyweight process.

Oracle independence: OD exact-snapshot shadow and journal scheduler have
different instrumentation, but share the unchanged solver and tested workload;
CD bulk/delta share classification assumptions; SU local/portable comparisons
share one causal graph; MP/DP test rules assume selected proof incidence. They
can discriminate instrumentation/transport/delta mistakes without proving the
source-generation or universal semantic premises. No seeds, enumerated ranges
or mutations were run by this audit. Unknown all-source coverage, unexecuted
future gates and missing approval detail are retained explicitly.

Blob IDs are Git object identities; SHA-256 below hashes exact document bytes.

| ID | Git blob | SHA-256 |
| --- | --- | --- |
| EF rescue | `bb736af8e0b5dee14104375dcb4546aaa87c93cd` | `88badc5212e3bc59ef350e5a27c0b08fbb972f1d4bcf3822707ccdef3bbbecc9` |
| OD | `e3929afc16f88c53571de51f172e60707b07e961` | `82fcb31b10a940927147602312e80edee9f84d38764287a3a814b4f31ad6c14f` |
| SS | `cb519e127e95425d1a59811b413190d8ff5a4d9b` | `dcd3eaabfecb41d124f3a7082f0fed4c757d600e8bae0bdd8c918a5011d08003` |
| OC | `7da42811920121877092a1af34fac46554b4fe71` | `aa49b05cbd1b817a4eb25928840353f3eb406064a0da886a2924ac7e6f7cd9c5` |
| PU | `4b56c1d4cf3e83829f3e370aa09bbfd3fa9e9d61` | `e11970e39a84b6869ec182980c6d058de5bfab9ded2f61460f054ec7d2ffe394` |
| SU | `1dea5d805c924ca966618a69c21407e2f096fa3a` | `ce57e1ba90d26f3799efcef5a62d8b0c97d2d30944322838cb7980c0581625c9` |
| DC | `d7f6e1ecddc94f22a3cc853378342836b5de9a0e` | `a06dfed930f0dbb5f3eeaf59a9d97008867910b4a373b4aaa9e8c0ebcc1b7324` |
| CD | `d439ee5d64845bc8d62316dcb555b3870ffe8752` | `7085de077af4ea43bbedf698dfaf04a8a21d01b3c60593d89a464221a61feef7` |
| MP | `d67411d2a630e52ad308d8b7e09d50c95b5e8d45` | `2d46038533b1c7c1fbf129e574abb49a9ec45d72ed0b2a1d8c7ec464c63df62d` |
| DP | `cec1ca9fad0e85db2d71942e2ec1a53d304c662b` | `80baae430af4f590598371e8947f6941af728dc42213a834d54fd90e6719d85d` |
| U3 | `0c5991a4ead79a4540c6c77f8c3a4e80e9973a58` | `121d598d91fe809582625e9541ed174aae81082922325283f9557c3f9e587952` |

All eleven assigned bodies are fully read; none remains unread. Not inspected:
compiler source, cited test implementations, every earlier revision body,
external session transcripts/approval conversations, unreachable/pruned Git
objects, separately leased root/cycle addendum, or current implementation
correspondence. Path histories establish only objects reachable from the queried
anchor/ref set, not absence of never-committed drafts or all lost history.

Recommended next action: primary obtains one bounded independent documentary
review of this frozen appendix, then incorporates accepted metadata/coverage/
dependency deltas into its catalogue and existing DAG without theorem promotion.

## Commit packet

- Exact leased/changed path: `notes/theory/oracle-inference-document-audit/appendix-batch-a.md`.
- Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Additional authorized rescue baseline: `5b7897bbc35573b3d496aab9d621647940e21894`; excluded from anchor authority.
- Direct historical dependency hashes: frozen table above; none changed.
- Claim/review status: documentary audit and conditional-premise inventory; frozen; independent review pending; no proof closure.
- Checks already run: contiguous full-body coverage, path histories, rescue ancestry/absence, exact blob IDs and SHA-256. No executable verification.
- Proposed message: `research: audit Oracle scheduling and provenance document batch A`.
- Shared-record deltas intentionally left to primary/curator: catalogue full READ/history/approval entries, rescue exclusion, SS abandonment, OD recording-policy succession, SU production/budget gaps, DC→MP→DP supersession, DP withdrawn allocation rank and U3-B retirement. No task/index/authority/question files modified.
