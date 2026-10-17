# NPAIR actual-argument ingress sprint closeout

Sprint: `npair-actual-argument-ingress-20261018`, rev1, contract
`c0754dc6de94c15e923ce24cc58b8208d0934dcf7bc92abcae34589185ec9d32`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original theorem,
source domain, quantifiers, receive route and C1/C2 retained.

## Outcome

Original parent conditions resolved: **0** (0 before, 0 after). H0, L2 `eta`,
P3/P6, actual `s1 -> D`, both ordered Replay inputs, F1/FK1, universal
compatibility and the parent theorem remain OPEN.

The proof artifact found that pinned Apply collection retains exact HIR
endpoints but initializes `native=None`, then delegates demand construction to
an unleased owner. The call observer requires an existing native demand. Fresh
spec review was CLEAN within this bounded finding; it did not establish an
actual call, parent edge or theorem closure. Artifact:
`notes/theory/2026-10-18-npair-actual-argument-ingress.md`, SHA-256
`c5365821565f8043f1d63fe50a209ce24777cf506a26098852f01db33d0d2d09`.

The contracted harness command ran once with the added source line and exited
0 on partial HIR with reported HIR diagnostics. The fixture was restored to
its exact baseline SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.
No compiler, test, fixture expectation or production source changed.

Independent implementation review found one MAJOR evidence overclaim: the
report inferred missing `received` LocalSource and collector coverage from
output that never queried that binding. The `UnsupportedExpression` diagnostic
does not establish absence or identify a lowering defect. The correction
withdraws those claims; independent delta review is CLEAN:
`notes/progress/2026-10-18-npair-actual-argument-source-path-correction.md`,
SHA-256 `071b87b2e08acf6845de2b8fd16199fe0c84590abda5fc2f4bb41aae7fa39586`.
The original submitted note and handoff remain immutable historical evidence
and are superseded on this point by that correction.

The two frozen lane handoffs are retained at
`tasks/agent-loop/inbox/20261018-npair-actual-argument-ingress.md` and
`tasks/agent-loop/inbox/20261018-npair-actual-argument-source-path.md`.
Their reported runtime details are not independently reconstructed beyond the
reviews described above. Full sprint budget 1800s charged; proof remainder was
UNKNOWN, so no prior budget rolls over. Astra 0.

## Next outcome

The successor sprint explicitly observes `received`'s binding, LocalSource,
Apply and operands through the research harness, while tracing the actual
Apply native-demand constructor and complete Function-child dispatch in
`shadow_apply.rs` and `lib.rs`. It does not presume HIR lowering is the cause.
It must tie the same returned `R1` and Written field `s1` to receive's `D` and
both actual ordered Replay inputs, or identify the first missing edge from
directly observed evidence. Parent theorem claims, source domain, quantifiers,
receive route, C1/C2, F1/FK1 and soundness obligations remain unchanged.
