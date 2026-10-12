# Oracle appendix audit D: sealed cache and read-foundation resequencing

Status: Frozen documentary audit; research only; independent review pending.
Audit date: 2026-10-12.
Scope: two historical Oracle documents, their retained revisions, scoped approval
records, definitions, invariants, withdrawals, and proof dependencies. No compiler
implementation or execution is evidence supplied by this audit.

## 1. Immutable sources and coverage

`O = a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Line locators below refer to these exact blobs, including historical appendices.

| Label | Exact source | Git blob | SHA256 | Full text read |
|---|---|---|---|---|
| S | `O:notes/design/2026-08-13-cpk-sv-d-sealed-conservative-cache-plan.md` | `c59a8c065739b28651044434fcb3391a8a1aa01f` | `d5768df7fb1970160c810446c21308866bf086378e4f66ca27897c9b9346af5a` | L1–3420; 216782 bytes |
| R | `O:notes/design/2026-08-14-cpk-sv-d-ss2-read-foundation-resequencing-addendum.md` | `1d7be51fe8733dc59b9a2b2870f7ea55507fa2ba` | `14cd42f63cd0ef2304d0ec2dc1dbc386ff2e77e1497e164c71cf0bf6d790bc7e` | L1–3067; 253549 bytes |

Both complete selected texts were read: **6487 lines**, including the rejected,
blocked, and later accepted sections. Truncated initial tool captures were replaced
by bounded line-numbered reads; missing intervals were read separately. Revision
coverage comprises every exact-path change reachable from the eight frozen
`corpus-refs.tsv` commits: one S ADD and one R ADD plus thirteen R modifications.
All removed revision lines were read; retained additions are covered by the full
final text. This is text/history coverage, not independent certification of the
historical reviews or source correspondences asserted in the documents.

Current transfer policy was read separately at
`e1dc2f4233b8fbf9aeaa2134778e244d890e0317:notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
blob `00b9bf7191c0d96cd64b5758ac8e7df5671cef25`, especially §§1–5 and Authority
and integration. It supplies current scope restrictions, not evidence about
historical Oracle behavior. Active `rules/design-authority.md` Authority order,
Legacy compatibility, and Approval and implementation gate; `research-lab.md`
Evidence quality and Commit conveyor; and `git-concurrency.md` Disjoint-file mode
govern this research artifact.

## 2. Exact creation, revision, deletion, and approval provenance

S declares **2026-08-13–2026-08-14**, final rev.9, at L3–9. Its first exact-path
ADD is `ac0639b2fc699785180b9bb69369c8db08bef372`, author and committer
`2026-08-14T09:02:59+09:00`. It was first committed as rev.9; rev.1–8 are
documented internal draft history, not separately recovered exact-path commits.
S has no later exact-path modification, rename, or deletion in the frozen corpus.

R declares **2026-08-14**, final rev.9, at L3–9, and retains dated August 15
appendices. Its first exact-path ADD is
`42304ba47f704d51bc81fc7bd0ee458aaaf36697`, author and committer
`2026-08-14T14:58:46+09:00`, first committed as rev.7. Earlier rev.1–6 history is
reported in R L22–49, not separately recovered exact-path commits. All following
author and committer times coincide; dates are Git metadata, not inferred approval.

| Commit | Date/time +09:00 | Retained documentary delta |
|---|---|---|
| `6a9fa0b8ddad9ecf79fa2cee3364884668c103a7` | Aug14 19:03:21 | Rev.7→9; narrow projection-side `pub(crate)` exception; conditional owned `pos_var_in_scope` |
| `857664069e442c55d397d1dc5d2dc84267a1771e` | Aug15 00:50:34 | Pending-receipt withdrawal; all-error post-commit terminalization proposal and second rejection/block |
| `a70fa5004a0ba378fa50441433d2e47ff34b73c1` | Aug15 05:44:02 | Third row-3 no-op proposal and rejection; publication is correctness-sensitive invalidation |
| `7471cf4f661e1ae9c0599f10446eb8ac518a8efd` | Aug15 08:41:41 | Fourth reachability-based row4/7 resolution, document-reported approval |
| `e14896ca5d59be1744c392d887fe4118e289a164` | Aug15 14:00:15 | Eight-getter witness/compaction proposal; four NOT SOUND reviews and blocked status retained |
| `9199da95c7c5bd22b336e4974babe99c15b5a124` | Aug15 15:17:59 | Fifth row1 strategy: attempt-local poison plus output gates, explicitly draft/unapproved |
| `872d1b9afb86a94fb34420ab8a8879719245b5ec` | Aug15 15:49:31 | Dynamic cross-crate gate fixture and complete unchecked dump inventory; intermediate pre-latch constructor |
| `6506161a046ec451fd0c344139787ae71190b7e7` | Aug15 16:07:03 | Withdraw pre-latch shortcut; require real gateway one-shot denial, precise CI/release and telemetry boundaries |
| `74b9571fc8cef6877a07b5b2467fdc21398c5ade` | Aug15 16:19:55 | Feature-only consume/bridge completeness; owned telemetry delta in actual yulang E2E |
| `de648fe969ecbf67dd7577af1dd8d7bf49f82f1a` | Aug15 16:33:03 | Complementary cfg branches; feature arm restricted to fixed failure/count; still draft, approval pending |
| `6085d75ba0f34c6647273faee3b2407780ace0aa` | Aug15 16:41:26 | Fifth-review unconditional SOUND report; expressly says implementation still needs user approval |
| `b1c02a4360d89aa7728ddedfe6b0ad23f5c51e16` | Aug15 16:43:21 | Separate user-approved signature/status replaces review-only status |
| `48f739b60e9d62b3c9f6eb24f68e7c1962fd64d4` | Aug15 21:25:30 | Fifth-strategy heading corrected from draft to confirmed/user-approved |

No R exact-path rename or deletion appears in the frozen reference union. This
does not assert that a path could never have been deleted outside that union.
`O:notes/design/INDEX.md` is absent; no approval is inferred from an index.

Approval is **document-reported, scope-specific**, not a recovered direct user
message. S L7, L11–16, L3417–3420 report independent review and user approval
August 14 for CPK-SV-D implementation under its slice gates. R L7 reports
August 14 rev.9 approval; its authority notice L13 still says draft/unapproved
until review/approval, and L1498 retains a stale draft footer. These inconsistent
markers are preserved. The later explicit scoped signatures identify row4/7
fourth strategy approval August 15 (R L2156–2162) and row1 fifth strategy approval
August 15 (R L3055–3067). The Git distinction between review-only commit
`6085d75...` and approval-marking commit `b1c02a...` is corroborating documentary
provenance, not a transcript receipt. Historical grandfathered design authority
within those scopes does not establish a mathematical theorem.

## 3. S: original definitions and contract scope

S changes snapshot-writer ownership, mutation finalization, and successful
structural-validity caching. It expressly retains CPK-SV-A/B/C identity,
late binding, support closure, fallback, error precedence and cycle semantics
(S L45–62). It does not define new source typing or generalization rules.

### 3.1 Defined objects

| Source | Original definition or mechanism |
|---|---|
| S §0.1, L68–136 | Sole structural owner; prepare→private prepared command→commit→single finalizer; default Changed; explicit command-specific Unchanged proof avoids invoking a mutating handler |
| S §3.1, L410–537 | `ProofAttemptNonce(NonZeroU64)` with process-global nonwrapping mint; `ProofAttemptKernel`; `ProofStructuralState`; `StructuralData` five families; `ProjectionRoundBinding { attempt, snapshot }`; authenticated reuse vs disabled reuse |
| S §3.1.1, L539–807 | Actual gateway-child storage/family-sibling privacy layout; restricted opaque query/round/handle types; private constructors, fields, tokens and success candidates; opaque scope-consuming `QueryCompletion<R>` |
| S §3.2, L809–930 | Caller-owned data-only `StructuralMutationIntent`, gateway-private `PreparedPayload`, reservation-owning `PreparedStructuralCommand`, `StructuralMutationDisposition`, applied receipt; exhaustive mapping/dispatch |
| S §3.3, L932–970 | `ExplicitNoOpProof::{UpperClaimMove, ExactDuplicateBound}` are candidates for a separately reviewed small allowlist; bounded exact comparator rechecks current local base and all relevant relations; initial allowlist empty |
| S §3.5.1–2, L1016–1113 | Cache snapshot is distinct from target/relationship-local semantic revision bases; `StructuralBaseStamp`, `ExpectedSlot::{Absent,Present}`, resource-domain keys, reservation claims and tickets; absent/present and ABA checks |
| S §3.5.3–5, L1115–1313 | Attempt-global unique ticket ledger; `physical_spare_capacity(domain) >= outstanding_units(domain)`; reserve total required spare, not deficit; pin outstanding empty child containers; consume one-shot reserved inserts/existing-slot witnesses |
| S §3.5.6–7, L1315–1517 | HRTB preparation scope and nonescaping handle; kernel arena ownership; `InFlightCommitGuard`; pre-write checks/staging; closed prepared publication plans and audited panic-free publication; cleanup is reservation ownership, not semantic rollback |
| S §3.6, L1519–1640 | Every evaluator/new override insertion fallibly reserves; checked preflight node count is not an evaluator-node bound after cache skips; query and publication evaluators propagate typed Result |
| S §3.7, L1642–2105 | Active attempt capability; kernel-latch→attempt authentication→matched round-latch→snapshot/memo/cache ordering; foreign round rejected without importing its state; HRTB exclusive query lifetime; lifetime-free owned round state with target-local facades; owned selected `SchemeProjectableLower` |
| S §3.8, L2107–2146 | `StructuralValidityCache { records, constraints }`; `ValidatedAt { snapshot, outcome: FullyResolvedStructuralSuccess }`; attempt-local, lazy, nonserialized; publish after top-level complete unwind/rechecks; Changed clears old snapshot cache; saturation disables reuse |
| S §3.9/§5, L2148–2305 | Late-bound `ValidateClaimBinding` and `ValidateCoverageRootState`; preserve CPK-SV-C interleavings; retain D0 snapshot type/saturation but withdraw scattered bump/tag/census as correctness authority |

The closed mutation vocabulary is: AdmitBound, PromoteBound, TombstoneBound,
AdmitConstraint, ExtendConstraintProof, RecordProofOccurrence,
AdmitProjectionSupport, AdmitProjectionFormula, AdmitUpperClaim, MoveUpperClaim,
ChangeLiveCoverage, UpdateRowReduction, AdmitRowDerivation, AdmitReplayRelation,
AdmitQualifiedParent, AdmitProjectionIndex, AdmitOriginIdentity,
AdmitWitnessIdentity, AdmitSchemeInstantiation (S L816–859). The exact production
vocabulary is an SS0 census requirement, not proved exhaustive by this list.

### 3.2 Exact numbered invariant inventory

S §8 inherits earlier CPK-SV invariants 21–36 and CPK-SV-C/CPK invariants, then
defines these **contract requirements**, not proved theorem labels:

| Numbers | Original names | Lines |
|---|---|---|
| 37–40 | Sealed structural ownership; Sealed read surface; Closed mutation vocabulary; Single successful-commit finalizer | 2772–2790 |
| 41–44 | Conservative Changed default; Private command-specific Unchanged proof; No mutation after Unchanged proof; No early-return escape | 2792–2809 |
| 45–48 | Prepare-before-write atomicity; Atomic snapshot publication; Saturating snapshot safety; Successful structural outcome only | 2811–2827 |
| 49–52 | Top-level cache publication; Evaluator insertion fallibility; Terminal latch precedence; Committed receipt authority | 2829–2847 |
| 53–56 | No partial-sealing cache authority; Non-structural sidecar separation; CPK-SV-A/B/C preservation; Evaluator memo separation | 2849–2863 |
| 57–60 | Optional cache allocation safety; No-claim preservation; Allowlist auditability; Trusted-boundary honesty | 2865–2879 |
| 61–64 | Changed-only value before allowlist growth; Single-thread completed-snapshot premise; Snapshot / conflict separation; Semantic-base precision | 2881–2896 |
| 65–68 | Outstanding reservation closure; Concrete Rust privacy boundary; Active-attempt access closure; Publication evaluator failure propagation | 2898–2922 |
| 69–72 | Kernel-owned prepared lifetime; Pinned-empty semantic transparency; Restricted cross-sibling visibility; Non-panicking authoritative publication | 2924–2944 |
| 73–76 | HRTB query lifetime closure; Prototype evidence boundary; Lifetime-free round persistence; Exact query-scope visibility and construction | 2946–2972 |
| 77–78 | Owned result boundary; Closed multi-container publication | 2974–2982 |

Quantifier boundaries matter: finalizer exactly-once covers every **successful
commit accepted by the gateway**, including accepted no-write operations; pure
read-only no-intent returns are excluded (S L1002–1014). Reservation closure is
per resource domain and every outstanding ticket, not just one writer class.
The read/exclusivity argument assumes synchronous single-thread operation
(invariant 62). It excludes arbitrary kernel edits, malicious editors, and a
future parallel query/mutation architecture.

### 3.3 Theorem and evidence status

S contains no named source soundness, principality, letrec, generalization,
extrusion, or global inference termination theorem. Its central “complementarity
theory” (S L138–158) is an architecture argument with explicit trusted premises:
all cache-relevant reads/writes inside the boundary, comparator completeness,
pre-write conflict checks, and semantic transaction atomicity.

The historical standalone Rust prototype `/tmp/cpk-sv-d-kernel-skeleton`
(S L268–308, L745–757) reports privacy/lifetime compile failures, nine unit tests,
one doctest, RAII cleanup, and a five-sample capability microbenchmark. It does
not verify proof-system semantics, real capacity, all payload construction,
the full call graph, or production exact visibility. That disposable external
artifact is not supplied/recovered by this immutable-document audit. Historical
tests and measurements were **not rerun**.

The retrospective validation-entry census (S §2) finds reuse opportunities, not
a speedup theorem. S §7 SS7 requires measured benefit before SS8 allowlist growth;
SS9 additionally needs oracle parity, resource limits, independent review and
user closeout. A final design signature does not show those implementation gates
completed. S §11.1 lists sixteen residual premise/engineering gaps, including
large semantic TCB, future comparator drift, migration/read completeness,
append-only TypeArena, capacity planning, panic-free publication, and owned
result/call-graph cost. None is hidden by a compile-fail check.

## 4. R: definitions, withdrawals, and accepted boundaries

### 4.1 Resequencing and original objects

R §7 replaces S §7 scheduling only: SS1→new SS1-RF→SS2-P0→SS2 proof/read
cutover→SS3/SS4/SS5→reduced SS6 reuse activation. Rev.9 separately modifies
invariant 76 visibility for enumerated cross-sibling projection callers.
S SS7+ production cache authority remains off until its own gates.

R defines `RoundReuseState<T>::SealingIncomplete | Sealed { snapshot, reusable }`
behind opaque `RoundReuseSlot<T>` (L169–232). Incomplete mode stores attempt
identity and projection terminal control but no cross-scope success-derived
checked/memo/override/cycle state. Target sharing occurs inside one immutable
scope; separate scopes start fresh. D0 snapshots are shadow metadata, not reuse
or conflict authority (R §4.3).

P0 `LegacyOnlyReadSources`, `LegacyOnlyQueryView`,
`ScopedLegacyProjectionQuery`, `ScopedLegacyPublicationQuery` preserve actual
legacy facts while moving caller boundaries (R L445–509). SS2 retires that route;
`PartialSealingReadSources` then selects exactly one statically chosen owner per
family, progressing to fully sealed input (R §4.2). No runtime old/new fallback.

Seven production round-owner contracts are enumerated (R L600–658):
scheme_projectable_lowers; expand_positive_aliases_in_scheme_compact;
record_scheme_projection_liveness_mutation; evaluate_record_inclusion_publication;
try_evaluate_projection_inclusion_snapshot; projection_inclusion_snapshot;
scheme_projection_record_is_included. Row1 has local/component witness and
input completion/hover subrows; row7 has distinct pre-mutation and post-mutation
clause-link phases. This is a minimum census, not a theorem that future callers
cannot exist. Sharing preservation requires scope hoisting to the logical pass
owner, not one scope per inner getter.

R §6 defines ownership layouts from Ss1ShadowLayout through ProofSealedLayout,
ProofBoundsSealedLayout, ProofBoundsConstraintsSealedLayout, RowsSealedLayout,
FullySealedLayout; actual non-Clone/non-Default `Legacy*Owner` values are consumed
by five family transitions. `FullySealedReadInputs` and
`AllFamiliesSealedWitness<'authority>` borrow actual fully sealed ownership;
`into_round_binding` obtains its gateway snapshot, not an arbitrary supplied
snapshot. **Rev.5 withdraws typestate-only mechanical exhaustiveness** (R L36–44,
L974–991): omitted fields, other owners, new mandatory reads and external closure
captures remain human census/test/review obligations. Witnesses encode ownership
of named families, not review approval or all-authority absence. SS6 activation
requires both structural and human gates (R L1235–1299, L1334–1358).

R §8 adds no new invariant number to the base rev.9; it maps existing 37–78
requirements to the reordered slices. P0 quantitative thresholds (R L677–717)
are measurement gates: matched-target raw-hit reduction exactly zero, aggregate
hit-rate decrease ≤1 percentage point, wall/RSS regression <5%, suitable A/A
noise, and unchanged output/error/owner/cycle/publication counts. They are not
asymptotic or semantic proofs.

### 4.2 Row4/7 failure history: preserve all rejected routes

| Route | Documentary status and decisive premise |
|---|---|
| Pending receipt / retry | Withdrawn NOT SOUND (R L1502–1507, L1907–1914): affine ownership permits silent drop; persistent busy denial has no lawful retry termination; enclosing event may already have committed |
| All post-commit errors become terminal | Rejected/block (R L1642–1690): assumed pre-commit propagation absent; earlier claim commits; ungated consumers; omitted defer caller; busy terminal mark can itself panic on the same RefCell |
| Row3 idiom copied after commit, no-op publication skip | Rejected (R L1887–1931): OwnersChanged is epoch/journal invalidation, not best-effort notification; skip permits permanent stale reuse and partial fence publication |
| Fourth reachability resolution | Document-reported confirmed/user-approved Aug15 (R L1933–2162): organic busy conflict excluded from safe synchronous production by asserted borrow/call-graph facts; use native RefCell borrow panic for invariant violation; same-self fresh-round construction excludes foreign rounds on named paths; release canary rejects synthetic/future nonterminal post-commit denial |

The fourth route does not prove foreign round misuse impossible throughout the
general safe API. K1-owned round passed to K2 is possible (R L1951–1956).
Same-self immediate consumption is a source/census premise, explicitly not an
owner-binding theorem (R L2064–2095). The release `assert!` on nonterminal
post-commit errors is a premise-violation detector, not a proof of reachability.
Real proof-semantic failure must already be latched by the gateway; only checked
in-repository consumers are in scope. These source facts were reported in the
historical document, not independently re-established against compiler code here.

### 4.3 Row1 witness/compaction: failed semantic fallback and fifth strategy

R L2164–2520 defines eight owned getters, inventories their real recursive
read sites, and retains a **blocked, four-times NOT SOUND** proposal. Its claim
that default compact is an empty-equivalent harmless semantic result is withdrawn:
`CompactRoot::default()` finalizes to `Pos::Bot`/Never and `Neg::Top`/Any;
unmodified formatter signatures cannot supply mutable scope ownership; formatter
failure lacks a post-check output gate (R L2497–2519).

The final fifth strategy (R L2521–3067) explicitly retains that failed history;
it neither redefines default compact nor retroactively approves the blocked
strategy. It allows **attempt-local poison**, with these exact internal results:

- Ordinary and negative scheme compaction: `CompactRoot::default()`.
- Recording merge compaction: `(CompactRoot::default(), Vec::new())`.
- Reachable role compaction: `(Vec::new(), Vec::new())`.
- Witness capture: `(Vec::new(), ProvenanceCompleteness::Incomplete)`.

No partial collector output, raw-mode fallback, retry, pending receipt, or second
quantification is allowed. The safety conclusion is output isolation, not
correctness of the poison value or incomplete witness. Poison may enter the same
attempt's cache/scheme/finalizer; that attempt must reach its checked terminal
gate without panic, nontermination, unbounded allocation or global semantic
mutation (R L2624–2656).

The eight purpose-specific owned getters (R L2587–2622) are
projection_upper_records_in_scope, pos_shape_in_scope, neg_shape_in_scope,
neu_shape_in_scope, role_constraint_raw_vars_in_scope, var_neighbors_in_scope,
pre_pop_effect_families_in_scope, subtract_facts_in_scope. Upper records preserve
evidence-first then ordinary insertion order. New neighbor/pre-pop/subtract
intermediates and some Neg clones have actual hot-path costs; GWCB performance
gates remain obligations, not zero-cost parity claims. Read instrumentation must
fire exactly once per logical read. No raw/general machine/arena/view access is
authorized.

Definitions added by the fifth strategy:

- Bounded mutable-owner reborrows; two public input-formatting Rust APIs change
  `&Arena`→`&mut Arena` (R L2658–2682). This is an explicitly scoped API break.
- Read-only `PolyCheckOutput::has_proof_terminal_failure() -> bool`
  (R L2684–2704), exposing neither failure variants nor latch mutation.
- Fixed one-shot `test-support` arm/pending bridges and synchronous
  `with_terminal_projection_query_failure_for_test`, returning owned
  `TestSupportProofSoakDelta` scalars (R L2706–2856). Generic arbitrary failure/count
  injection remains cfg(test); feature-only consume and telemetry branches must
  be present and their cfg complements symmetric.
- Three final **post-format** gates: source_hover_from_check→None;
  source_completion_from_check→empty; source_member_completion_from_check→empty.
  No later query/format may occur (R L2858–2878). Ordinary LSP keyword fallback
  may remain; type-derived candidate/detail output is suppressed.
- Attempt-local GeneralizeCompactCache, scheme, witness, provenance and arena
  ownership; only gated final request results persist (R L2880–2903).

The test seam distinguishes a real gateway query denial from a pre-latched
constructor or boolean helper override. Its declared CI graph may compile the
seam; production caller edges must remain zero; the supported shipped release
graph excludes the feature. Feature-only organic/intentional telemetry delta
must be 0/1 in actual yulang E2E. These are proposed/approved verification
requirements, not runs performed by this audit.

Fifth-strategy invariant inventory, R L2969–2990: **1** No semantic claim for
poison; **2** Latch-before-poison; **3** Attempt isolation; **4** Checked initial
output; **5** Checked post-format output; **6** Same-self round locality;
**7** One scope / no fallback authority; **8** Exact safe surface; **9** No new
recovery protocol; **10** Normal-output parity; **11** Public-surface scope
precision; **12** Test seam isolation; **13** Telemetry isolation. These local
numbers are not additions to the parent 37–78 sequence.

The final text reports four SOUND WITH GAPS reviews followed by an unconditional
SOUND design review (R L2544–2557, L3055–3067). This is a historical architectural
review verdict within stated premises, not a formal source soundness or cache
equivalence theorem and not independent review of this audit.

## 5. Explicit premises and documentary implication chains

No named formal theorem with source-program quantifiers is proved in either
document. The strongest reusable implications remain **conditional mechanism
claims**. Their quantifiers and dependencies must not be promoted.

### 5.1 Structural-success cache implication

For every successful validation of a record/constraint `x` within one active
attempt, suppose (i) canonical structural validation depends only on the sealed
mandatory facts plus the verified immutable type-shape exception; (ii) every
relevant mutation is reflected by the sole completed-snapshot finalizer, or a
correct full comparator proves it unchanged without mutation; (iii) same
attempt/snapshot identifies the same facts; (iv) the success was fully resolved,
top-level unwound, and cycle-independent; and (v) terminal precedence is enforced.
Then reuse of that structural-success marker can omit repeat structural
validation of `x` without changing its structural-success result. This is the
documentary architecture's argument: stable inputs plus retained complete success
give stable deterministic validation. Determinism of the canonical validator is also a required premise. It does **not** establish (i)–(v), a projectability/evidence
result, source inference soundness, or overall termination. Source validation and
cache share the same semantic contracts; forced-uncached comparison alone is not
an independent semantics oracle.

### 5.2 Poison isolation implication

For every actual denial on the fifth strategy's named same-self pure-read
traversals, suppose (i) all organically reachable denials latch the same attempt
before poison is returned; (ii) no poison escapes that AnalysisSession or causes
unsafe/nonterminating work before the boundary; (iii) all checked initial and
post-format output paths gate the sticky latch, with no later formatting; and
(iv) persistent artifacts/request cache only consume gated results. Then no
poison-derived type output from that failed attempt is published on the named
checked graph. The argument is causal isolation, not poison semantic neutrality.
Incomplete provenance values alone do not distinguish failure from normal
incompleteness (R L2882–2884).

Its original domain excludes arbitrary public/external composition and eight
unchecked dump surfaces (R L2905–2929): dump_loaded_file, dump_loaded_file_raw,
dump_source, dump_source_raw, lower_loaded_file, dump_lowering,
dump_lowering_raw, dump_lowering_in_module. The actual unchecked base chain can
produce poison-bearing BodyLowering without a terminal check; zero current
in-repository production callers is reported, not a universal public API safety
claim. External unchecked lowering-to-artifact composition is also excluded.

## 6. Dependency edges and current Simple-sub transfer

All dependency blobs below are pinned at O. They are locators for neighboring
audit owners, not an assertion that this two-document lane fully read them.

| Dependency | Blob | Required edge |
|---|---|---|
| `notes/design/2026-08-12-cpk-preflight-structural-validity-addendum.md` | `171bb10c044e53d49c2b5f1e745e539fe483ff9f` | CPK-SV-A certificate, B order/fallback, parent D scope and inherited invariants |
| `notes/design/2026-08-13-cpk-sv-c-dynamic-dependency-synchronization-addendum.md` | `6b39e4b2123120d3bd063079ea1fabc5fa52a664` | Stable obligations/current claim-live late binding/support closure; receipt and Phase A/B semantics; approved interleavings |
| `notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md` | `6ac4d2cdf2108c84dc28da008d787bf964a43e9e` | Root ownership and active-path cycle semantics; no snapshot-success→evaluator result inference |
| `notes/design/2026-08-02-mpc-dpn-projection-evaluation-round.md` | `ec7d8df6cd093a427b3a044858d4a95436c99ee4` | Round lifetime, cycle-cut sharing disable, fresh mutation-separated evaluation |
| `notes/design/2026-08-10-generalized-witness-claim-bridge-provenance-gap.md` | `3bc5bde8daf5baeeb3c2d5cec09ea71b19743036` | Witness/provenance consumer completeness and hot-path performance requirements |
| `notes/design/2026-07-13-role-impl-method-two-stage-lifecycle.md` | `1c97f0ba68367af2cc46601a3f1679627de5eede` | Quantify once, retained scheme/witness lifecycle; output isolation does not prove conformance/generalization |

The source/construction ownership chain described by these documents is:
constraint/bound/row/identity/proof constructors → typed prepared bases and
reservations → committed structural ownership/receipt → epoch/invalidation
publication → snapshot-authenticated structural validation → separate
projectability/evidence evaluation → scheme compaction/witness/generalization
consumers → checked attempt and post-format publication gates. Each arrow needs
actual owning-source evidence for implementation transfer. This audit identifies
that chain without claiming to verify compiler code.

Transfer to current Simple-sub is limited to useful obligations: one authoritative
owner per fact; invalidate dependent cached results on every relevant mutation;
separate cache identity from semantic conflict; scope memoization by actual
attempt/state; preserve complete original constraints and normal generalization;
prevent failed private results from publication. These can inform proof and
construction, but the old CPK proof graph, snapshot scheme, reservation machinery,
exact diagnostic precedence and Oracle failure protocols are not automatically
current algorithm requirements. Current principles §§1–3 require proving the
selected Simple-sub operations/invariants; §§4–5 permit safe private-attempt
discard and reject unconditional full restoration/rollback goals. Neither
document closes current directed effect hygiene, letrec, principality, extrusion,
termination, complete Call, or source-to-proof correspondence.

## 7. Checks, limits, and handoff

Commands were read-only `git show`, `git rev-parse --verify`,
`git log --full-history --no-renames` over the frozen corpus refs,
`git diff-tree --root --no-renames`, and parent→revision `git diff`, with in-memory
Python hashing/metadata extraction and bounded line-numbered text output. No
compiler code was inspected as governing semantics; no tests/builds/probes,
measurements, runtime mutations, or Git mutations were performed. CPU/RSS and
wall-time usage were not instrumented. Source bytes/hashes and all fifteen
exact-path change events were checked; no unrecovered assigned document remains.

Unverified: historical direct user receipts; independently reproduced historical
reviews/prototype/measurements; all asserted source call-graph, read completeness,
capacity, no-panic, attempt-isolation and gate reachability premises; full
neighboring dependency texts in this lane. Current authoritative policy is
separate from historical approval provenance. This artifact supplies a complete
documentary claim inventory, not a new mathematical proof or production approval.

Recommended next action: primary integrate both rows as full selected-text reads,
preserve the reviewed-design vs proved-source distinction, and keep the exact
cache-read completeness/poison-isolation source bridges owned separately.

### Commit packet

- Exact lease: `notes/theory/oracle-inference-document-audit/appendix-batch-d.md`.
- Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Direct dependency hashes: S/R and neighboring blobs above; immutable, unchanged.
- Claim/review status: frozen research documentary audit; independent review pending.
- Checks already run: full 6487-line text reading, frozen-union exact-path history,
  all removed revision lines, source Git-blob and SHA256 checks; no compiler tests.
- Proposed checkpoint message: `Audit Oracle sealed-cache and read-foundation appendices`.
- Shared deltas left to primary: catalogue coverage/status, README/DAG links,
  task/progress records, review adjudication and Git integration.
