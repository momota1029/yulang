# Cycle220: explicit actual-head sharing and V8 rejection

Status: Draft proof design implementing owner decision I-41 / spec6.5.

Recover from integration383a65520, not the inaccessible cycle219 code. New code
must be checked anew. Keep existing sources unchanged; append imports/audits.

Data: pairs of occurrences of the same head variable, their actual origins
under a current Frame, and equations between their total interpretations.
Independent judgment: all repeated-variable actual-origin values agree.
Show that the existing actual head schema already entails this judgment; do
not assume constructor injectivity. Expose it in packet/effect equivalences.

V8 adds a sharing-conflict rejection predicate to V7. A conflict has a unique
endpoint-selected declaration, a current model and eligible frame baseline,
and no compatible current model/frame satisfying the sharing equations.
Ambiguity keeps priority; no new pending rule. Operational Step should remain
unchanged if equivalence with existing packet constraints is established.
Transport all operational laws and the one-premise EvidenceNode composition.
The latter remains OPEN until independently proved, not an axiom or hidden
assumption. GroundCopy218 must be explicitly rejected in the new boundary.

Work ownership: new B4TargetV8/B4SkeletonV8; new HeadSharing220; new concrete
boundary/transport/regression modules. Parent alone edits imports/Audit/report.
