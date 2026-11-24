import Yulang.GeneralDeclarativeI65SameEventSemantics388

set_option warningAsError true
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree)

section
variable [judgment : ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

#check (aligned_same_event_semantics :
    ∀ {P : LiteralEvent s → Prop} {replay : LiteralTreeFrom tree t lowered},
    CanonicalDictionaryReplay replay →
    TreeMeaningOver P lowered →
    ∃ events : LiteralEventTree (s := s),
      ExactReplayEvents replay events ∧
      ExactOrderedOccurrences (dictionaryTree d) events ∧
      orderedLiteralReceipts events = written ∧ LedgerMeaning P events)

#print axioms Yulang.GeneralDeclarativeI65.aligned_same_event_semantics

end
end Yulang.GeneralDeclarativeI65
