import Yulang.GeneralRebaseReceiptCheckedReplay289

#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.installed_tick_exact
#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.replay_agrees
#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.positive_replay
#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.pending_replay
#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.actual_stale_row
#print axioms Yulang.GeneralRebaseReceiptCheckedReplay289.observes_exact

#guard (Yulang.GeneralRebaseReceiptCheckedReplay289.replay true).1 == ["receipt", "published"]
#guard (Yulang.GeneralRebaseReceiptCheckedReplay289.replay false).1 == ["inspection-pending", "none"]
#guard (Yulang.GeneralRebaseReceiptCheckedReplay289.replay true).2 == some ⟨2,0,1⟩
#guard (Yulang.GeneralRebaseReceiptCheckedReplay289.replay false).2.isNone
