# R99 failure-boundary selector proposal — no lease

Dispatcher: `/root/r99_front_selector` (read-only follow-up).

Observed R99 receipt: the single authorized run exited 101 after one test; the positive cell returned `Unavailable(HandlerEvidence(occurrence 3, range 87..123))`; the negative cell was not reached. Static proof and independent compiler/source review identify the same fresh receiver / missing RootComp boundary seam. R99 remains frozen; no retry, repair or production edit.

Proposed strongest next outcome: one separately authorized R100 finite correction for receiving evidence on the remapped fresh receiver, tied to the unchanged R99 source and a paired negative. This is directly runnable-source work, not an open-ended storage/fiber investigation.

Proposed proof lane: derive the finite boundary transport and its exact owner/view/receipt premises; test wrong/sibling permission as a falsifier. Then inspect whether R95 method/role source identity can be connected to a real source/runtime behavior path, or record an owner-specific `NO_SAFE_CODE_SLICE`.

Proposed implementation paths: `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/runtime/receiving.rs`, new `tools/inference-playground/tests/runtime_receiver_replay.rs`, and one implementation handoff. Proposed proof outputs: `notes/theory/2026-10-19-r100-receiver-replay-correspondence.md` and one proof handoff. These are suggestions only; no R100 lease was issued by the selector.

Budget proposal: total 3,000 seconds, Astra 0, one Luna-owned run of at most two distinct commands at 120 seconds each, preserving three UNKNOWN identities, quarantines and review capacity. R99 closeout/current state were not read by the selector in this runtime snapshot and need Luna synchronization before dispatch.

Original Simple-sub/evaluator quantifiers, A/B, F1/FK1, R50/R85, adoption and production gates stay open. After this one bounded receiver fix, the selector recommends rotating to method/role behavior with proof or another hygiene front; do not auto-repeat similar effect repair packets.
