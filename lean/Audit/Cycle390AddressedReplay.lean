import Yulang.GeneralDeclarativeI65AddressedReplay390

namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree)

section
variable [judgment : ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

#check (exact_replay_ledger_addresses :
    ∀ {replay : LiteralTreeFrom tree t lowered} {events : LiteralEventTree (s := s)},
      ExactReplayEvents replay events → AddressedDictionaryEvents s q d events)

#check (addressed_replay_has_canonical_order :
    ∀ {events : LiteralEventTree (s := s)},
      AddressedDictionaryEvents s q d events → ExactOrderedOccurrences (dictionaryTree d) events)

#print axioms Yulang.GeneralDeclarativeI65.exact_replay_ledger_addresses
#print axioms Yulang.GeneralDeclarativeI65.addressed_replay_has_canonical_order

end
end Yulang.GeneralDeclarativeI65
