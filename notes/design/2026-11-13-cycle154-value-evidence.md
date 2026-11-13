# Value-supported current dictionary evidence

Status: conditional soundness extension, cycle 154.

Target: reduce the concrete additive `GeneralNominalValueBoundary` evidenceNode
obligation. Its installation guard is stronger, so its Stable predicate cannot
be converted to support/feedback stability.

For any registry, tracked state, selected root key/children, value stability,
and Joint, construct the exact current packet from a real branch. Extract the
value DecisionGuard from selected; its support and Supported proof also satisfy
the packet guard for that packet. Value stability now implies Committed.
Committed supplies every final-model Instance and actual generated children.
For reachable states, the exact ledger supplies merge closure using the
unchanged merge transition. Consequently only Joint remains as the extra
applicability premise. Child evidence uses the same final model throughout.

No old definition is changed. This is not the general evidenceNode proof:
Joint for arbitrary reachable journals remains unproved. No termination,
new language semantics, or full-language completeness claim is made.

Packet-free specialization: erase the actual value trace to the existing
reobservation trace (not stability). Its empty-journal shape supplies Joint;
exact ledger merge closure and the newly constructed value packet prove all
selected generated focuses terminal and sound, with no extra Joint premise.

Verification: focused `lake build Yulang.GeneralDictionaryValueEvidence --wfail`
passes (674 jobs); `lake env lean --trust=0 Audit/Cycle154Value.lean` passes for
all 12 theorems, depending only on the standard propext/Classical.choice/
Quot.sound axioms. No full build was run. This is proof-level correspondence
between existing formal definitions; no new Yulang2 execution claim is made.
