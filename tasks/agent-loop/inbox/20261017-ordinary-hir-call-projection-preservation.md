# Frozen handoff: ordinary-hir-call-projection-preservation

Sprint: ordinary-hir-application-admission-implementation-20261017, rev1.
Contract SHA-256 `a9220bc8dab9019a3b8d362ea6ed447cdbc0e70373f2b10845e6b02b8d8cc496`.
Adopted rev4 SHA-256 `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
Assignment/handoff ID ordinary-hir-call-projection-preservation, revision1.
Artifact `notes/theory/2026-10-17-ordinary-hir-call-projection-preservation.md`.
Artifact SHA-256 `226d389d8fb68b6ddec328dd0f6ece4a4f3f2e344eff3f434d10b0a3d02b37ad`.
Actual worker/sole author `/root/astra_accepted_call_hir_projection`, current-session.
Requested gpt-6-astra / medium; observed model/effort UNKNOWN / UNKNOWN.
No descendants. Baseline/checkpoint supplied b1f15a81a; source baseline in
contract5fbceb68d. No Git verification. All57 frozen dependency pins verified;
manifest includes the original48 source-audit pins, current direct owners,
adoption and parent-supplied exact Call/FORWARD-FIRST-CALL sources.

Outcome: mathematical output-size lower bound plus independently valid candidate
structural preservation lemmas. Independent review NOT_RUN; no production claim.
STOP full adopted-resource claim at the mismatch; do not call the structural
preservation theorem impossible and do not narrow admitted grammar.

Counterexample: E0=Name(f), Ei=Apply_ml(E(i-1),Name(xi)), all names unresolved.
V=2m+1 nodes, D=m+1 authentic errors, but each Apply_i.errors stores i+1 IDs.
R=sum(i+1)=m(m+3)/2 independently owned Box<[HirErrorId]> entries. This satisfies
ordered duplicate-free subtree error lists without duplicating any HirError.
It falsifies linear total retained-entry/work accounting in V while retaining
rev4 subtree aggregation and flat owned slices. It is algebra/source-schema
evidence, not an executed compiler counterexample.

Preserved lemmas: explicit Atom/retained Group/Apply_ml/Apply_call preflight and
resolution judgments; induction preserving associated child order, lexical
atom targets and exact node/key ownership; root occurrence belongs to outermost
retained constructor; distinct canonical descendants allocated after unchanged
carrier pass; checked same-key/conflicting-root handling and atomic append_stage;
whole-shape refusal before name diagnostics; dense final event-log indexing and
correct subtree error references. These remain valid with sufficient checked
allocation and an output-sensitive accounting. Proposed repair only:
O(V) node/worklist control plus O(R) aggregate-reference output, total O(V+R)
plus spelling/unchanged module costs, worst O(V²). No cost/storage repair adopted.
The proof does not claim current unmodified lowerers already implement it.

Concrete application: apply's f resolves to its existing formal; f1 retains
callee/argument keys at26..27/28..29 and tail key28..29. Answer in the full
three-definition namespace resolves apply/id to their separate module DefIds
at43..48/49..51, tail49..51. Under adopted projection both have empty structural
errors, preserved body roots and new descendants after carriers. The isolated
answer fragment without that namespace does not have resolved names.

Parent application: SOURCE-OPERAND-INCIDENCE supplies authentic structural
callee/argument and lexical occurrence identification for the original
Call-interface constructor. It does not supply independently typed original
reference, whole-carrier/context, license/provider/response/future contracts.
The exact first ordinary executable consumer still marks Apply/Group bodies
Error and records ApplicationTypingRuleUnresolved in ConstraintBatch::collect;
CandidateInference/source crosswalks are separate private paths. No sourceT,
semantic Call, native Result adequacy or MODEL follows.

Prior theorem reuse: reviewed local FORWARD-FIRST-CALL for the annotated
Unit-arrow receive source remains valid under independent Function/context and
one anchored joint MODEL. The integer/unannotated instances here provide none
of those missing premises. Its local result is not FK1; original A/B,F1/FK1,
N-Transport, complete Call, soundness, principality and termination quantifiers
remain unchanged. Original theorem conditions discharged0; new behavior executed0.

Mutual TODOs:
- RESOURCE-R-1, Luna: adjudicate adopted§2 linear-entry versus§4 aggregate-list
  mismatch using E_m before dependent implementation; output-sensitive bound is
  proposal only. Do not remove errors or cases to obtain linearity.
- PROJ-IMPL-1, separately leased implementation after review/adjudication:
  checked complete shape/key preflight, stable carrier inputs/ordinals,
  post-carrier canonical IDs, correct root Group key, dense event references and
  non-overwriting atomic publication. Falsifiers: wrong retained root key,
  swapped/equalized operand identities, early allocation shifting carriers,
  unsupported child emitting speculative name errors, sparse/foreign error IDs.
- CALL-SOURCE-NEXT-1: use the exact source incidences in independently typed
  source-interface and actual constraint/consumer correspondence, retaining
  complete original contextual/response/provider/future premises.

Checks/resources: static source reads, manual induction/algebra, SHA-256 only.
No code/tests/builds/probes/Cargo/Git/central records/external contact.
Clock start09:20:45 UTC, artifact-freeze checkpoint09:27:05 UTC:380s wall elapsed.
Conservative charged420/720s including freeze/handoff; remaining300s unused,
not a claim of continued work. Exact CPU/active duration UNKNOWN. Full resource
claim stopped at acknowledged counterexample; no new source expansion afterward.
Five substantive stages: authority/source reconciliation, constructor judgment,
identity/error/carrier preservation, lower-bound falsification and parent
application, freeze. Prior assignments' budget is not charged to this fresh one.
Three inherited UNKNOWN reservations untouched.

Exact new paths: artifact above and this inbox; scratch paths none.
Writer state STOPPED after freeze; all writes cease with this handoff, no
waiting-stage work and no descendant leases. Pending independent review/Luna
intake; no self-certification. Next action is RESOURCE-R-1 adjudication and
review of the frozen counterexample/lemmas before dependent implementation.
