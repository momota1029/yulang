# Frozen assignment handoff: accepted-call-hir-projection

Sprint-ID: accepted-call-hir-admission-contract-20261017.
Contract revision: 2; SHA-256 `f92c1269f47ae1ba3c002244f7254ebc7792af5270ad6a634f033e91323cf19a`.
Assignment-ID: accepted-call-hir-projection; handoff revision: 1.
Artifact: `notes/theory/2026-10-17-accepted-call-hir-projection.md`.
Artifact SHA-256: `0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`.
Outcome class: candidate source-native-evidence (source/HIR inspection only;
no native solver evidence), with explicit CST-shape premise and admission obstruction.
Review/production status: NOT_REVIEWED / NOT_AUTHORIZED.

Parent: original inference/execution outcome; full A/B, F1/FK1, N-Transport,
Call, soundness, principality, termination and source/native quantifiers remain
OPEN. Parent application: structural association does not imply zero HIR errors;
carrier retention cannot discharge the failed gate. Original premises discharged: 0.
New compiler behavior executed or established by a run: none.

Baseline supplied by Luna: `577172e30fe9e282f910cb5ff8267a42beea4a75`;
contract checkpoint supplied by Luna: `328f813d9`. All 14 rev2 direct pins were
rehashed successfully before writing. Exact paths/hashes appear in the frozen
artifact's dependency manifest. No Git inspection; baseline is supplied provenance.

Role/author/actual worker: astra_prover / `/root/astra_accepted_call_hir_projection`.
Session: current-session. Runtime receipt: parent NEW_TASK and subsequent rev2
resume acknowledgement to this actual worker; active source reads/hash checks
and leased artifact write completed. Requested gpt-6-astra / medium;
observed model/effort UNKNOWN / UNKNOWN. Sole author; no coauthors/descendants.

Result: association gives M(f,1) and M(apply,id); lexical f is apply's formal,
while apply/id in answer are module definitions. LocalSource retains the distinct
source occurrences. `local_source::form` returns Unsupported simple-body
projection for both non-atom chains; `module::lower_body` emits
UnsupportedExpression with Value(def_id) attachment and diagnostics. Ordinary
`lower_simple_chain` independently rejects them. Experimental resolved Apply
retention also deliberately emits UnsupportedExpression, and its inventory
expects nonempty errors. Under the explicit source-CST shapes, static prediction
is two diagnostics (apply then answer), not a newly observed error dump.

Source/consumer path: association -> carrier/identity -> simple-body projection
-> lower_body/ErrorSink -> hir.errors assertion. The prior run stops there;
constraint generation, propagation, candidate export/FreshUse/native consumers
are unestablished. Exact token ranges and owner-defined node ranges are separated;
numeric CST keys and trivia-bearing node ranges were not observed. General
left association is proved by cursor induction within the association contract;
this does not prove parser constructors emit the concrete shapes.

Remaining clause/owner: HIR-APP-ADMISSION-1, Luna's HIR design lane, with code
owners lower_body/lower_simple_chain/lower_plan and shadow inventory consumer.
Specify application admission, representation, identities, operand errors and
resource boundary; obtain required review/adoption before implementation.
Alternatives in artifact are proposals only. HIR-APP-CST-1 asks for an authorized
exact CST/source-key receipt or parser-owner audit before full concrete source
correspondence promotion; no execution is authorized by this TODO.
Falsifiers: fixed source retains application UnsupportedExpression after an
approved admission change; wrong callee/argument association or identity;
recovery/resource refusal publishes partial success; concrete CST contradicts
the two unary MlArgument chains. Mutual TODOs preserve the original parent.

Reused: prior failure receipt/closeout and structural/ownership authorities
within their scopes. Rejected: treating no parser recovery, associated structure,
carrier formation, or a shadow Apply inventory as error-free admission or Call
semantics. Historical hygiene/frame proofs are not needed or newly certified.

Checks/resources: all 14 dependency hashes and contract hash match; manual
source analysis; six substantive stages. No tests/builds/probes/Cargo/Git,
production edits, descendants, external contact or scratch paths. Initial
`python` hash utility invocation unavailable; `python3` retry succeeded.
Conservative charged budget: full 480s reservation, remaining 0; actual active
duration UNKNOWN (not a measured 480s claim). Unused reservation retired; no
pause/reset carryover. Three UNKNOWN writer reservations untouched.

Exact leased/new paths: artifact above and this inbox only. No other new/scratch
paths. Writer state: STOPPED after freeze; all writes cease with this handoff.
No unresolved descendant leases. This self-reported cessation does not certify
proof acceptance. Next step: Luna's already-granted independent compiler review,
then narrow admission draft. No further worker stage while waiting.
Commit-ready status: frozen research candidate pending independent review and
Luna intake/integration; no parent closure or production promotion.
