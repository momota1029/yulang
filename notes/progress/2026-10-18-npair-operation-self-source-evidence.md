# Operation self source-evidence owner audit

Sprint: `npair-operation-self-source-realization-20261018`, contract rev1, SHA-256 `66df3255cc83d18009238dc4e7e18ff4963003ebc8beb6f489f526de1f8fba19`.
Assignment: `NPAIR-OP-SELF-SOURCE-EVIDENCE-20261018`, implementation lane, requested Luna/implementer/high, cap 720 seconds; observed effective model/effort UNKNOWN/UNKNOWN. No descendants. Baseline supplied by Luna: `b3a9b1739b59d8c7991b5f798e98f71f96904b19`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN; original source domain and quantifiers unchanged; closure 0.

## Outcome

`NO_SAFE_EVIDENCE_SLICE`. No compiler owner was edited and no focused check was run. The exact leased APIs do not expose an authentic path from this fixture's emitted Operation self member to a consumed formal Permission. Reporting both source occurrences as one transition would manufacture a relation absent from the inspected owners.

The accepted working rule is the frozen C1/C2 candidate, SHA-256 `c8c9854c32cdb3dc5e9fe8e1be15293e3b05bb0b393daff3632f9ba516df1455`. This source result neither establishes that the implementation realizes the rule nor proves compatibility, `At`, parent membership, or parent closure. C1/C2 remain a working research rule; compatibility/WZ/P1–P6 remain open.

## Exact owner audit and data gap

Both pinned owner hashes matched before inspection:

- `crates/yu-solver/src/candidate_effect.rs`: `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212`.
- `crates/yu-solver/examples/research_source_registration.rs`: `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c`.

In `candidate_effect.rs`, `candidate_operation` enters the actual `candidate_signature_value`/`candidate_signature_effect` emitter. At an Operation root with omitted result-effect row, `candidate_signature_effect` prepends the declaration family as member 0 and stores the view with `OperationOrigin` (declaration, occurrence and retained payload). The view representation stores `allowed: Vec<SourceEffectId>` and one whole-view provenance; it does not tag each member's origin. Thus an explicit same-family written member would be indistinguishable by family ID alone. This fixture's root row is omitted, so its emitted root view would not have that same-row duplicate ambiguity. Its nested returned Function has a separate written `[ctrl]` row at a different `SourceNodeKey`; this is a different field from the root self view. The fixture has no callback or symbolic tail case to observe.

The formal annotation path constructs private `FormalPermission` records with parameter, occurrence, source owner, scope, typed Function path, source row and concrete family IDs, then retains them in private effect-algebra state. The record's code comment explicitly says it is local source permission and that authentic arrival consumption remains open. No public/example accessor exposes those records or a consumer result.

The pinned example authenticates the resolved `ctrl::choose` occurrence, solves the HIR, checks candidate ownership/conflicts, and exports only `f0`'s definition root. It does not read the private Operation view or formal Permission. More importantly, the fixture defines `f0` and separately defines `receive (f: ... [ctrl] ...)`; there is no `receive f0` application. The self view and formal Permission are therefore separate source facts with no actual provider/consumer edge between them. Capturing each with provisional logging would not establish the requested self-to-Permission path.

Historical evidence reused with limits: `notes/progress/2026-10-17-source-authentication-admission-run.md` and `notes/progress/2026-10-17-receive-first-refusal.md` identify the same fixture bytes (`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`) and record an earlier `CandidateInference::solve` refusal at formal-annotation preflight. That execution is prior evidence, not a claim about current runtime behavior. The current packet's accepted-use premise was not re-established by this audit, and no new Cargo check was authorized or run without an authentic evidence slice.

## Next owner request and falsifier

`NPAIR-FORMAL-PERMISSION-CONSUMER-20261018` — Luna to identify and, if authorized, lease the source action owner that connects a formal Permission to an actual provider/receiver constraint in an accepted source entry. First missing evidence: one authentic occurrence where the same Operation reference and `theta` reach the declared consumer, with member-level source origin retained through generated constraints and the actual Permission consumer. Proposed output: owner-grounded trace or a precise refusal boundary. Falsifier: separate declarations are paired by family equality, a test manufactures an assumed edge, or permission is inferred without the original consumer action. No owner outside this packet was inspected or edited; this TODO requests no authority itself.

## Checks, resource and writer state

No check ran: the only focused fixture check would stop at the observed API gap or require synthetic instrumentation not backed by a source/consumer edge. No broad build or test was run. The two compiler owners remain byte-identical to their pinned hashes. Work was static owner/source review only; exact active seconds were not separately measured. No scratch, generated output or temporary file was created. Writes stopped after this note and its frozen handoff.

Parent/source/native status: source map inspected; source-to-constraints-to-propagation-to-execution contribution NOT_ESTABLISHED; formal Permission consumer NOT_OBSERVED; proof/source correspondence NOT_ESTABLISHED; `At` and parent membership NOT_ESTABLISHED; parent closure remains 0.

Frozen handoff: `tasks/agent-loop/inbox/20261018-npair-operation-self-source-evidence.md`, revision 1, SHA-256 `471aa20c3df46b2232c9784596e627bf632b209664ecf01c566ddf05e5264893`.
