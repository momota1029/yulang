# Sprint R200 — source registration and qualification audit

Revision 2. Status: CLOSED, source registration construction established; provider-Capture path open.
Branch / baseline: `research/simple-sub-intrusion` / `5870fe8dd9b66b7d27e8632c9e606c3cf7b988f3`.
Authority: computation-forwarding preservation parent §§1, 6–7 and the existing R183 frontier obligation. No semantic change or production authorization.

## Outcome

Inspect the previously unpinned `candidate_value_graph.rs` owner for source registration, sealing, and qualification. Join its exact behavior to the current `candidate_source.rs` seed selection and `candidate_intrusion.rs` qualification call sites. Decide whether this supplies R177's earliest unestablished source-coverage premise or names the next missing producer/consumer edge. Preserve the original universal source domain.

Success evidence: an owner table with exact source key/slot registration, sealed representation, qualification predicate, and actual callers, plus a source-bound-to-provider application or a precise remaining field. Source IDs, fixture success, and absent lookup alone do not prove universal coverage.

## Exact boundary

Read the four pinned files only, plus R177/R183 receipts for the parent application. Revision 2 adds the exact source-seed owner, which R177 identified as the immediate consumer of the checking-occurrence map. Pins at revision 2:

- `candidate_value_graph.rs`: `7ba8d2a38487e5ad204fc6b19a3aa5a6f4984ee03249a9fc2210ee01993594ae`
- `candidate_source.rs`: `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a`
- `candidate_context.rs`: `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733`
- `candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`

Read-only. No source edits, tests, Cargo process, observer changes, or subagents. Exact writes: this contract, `tasks/agent-loop/current.json`, and `notes/theory/2026-10-21-r200-source-registration-qualification.md`. Solo primary because the user explicitly selected no subagents. Budget 300 seconds, no carryover. Preserve all A/B, source/native, and production gates.
