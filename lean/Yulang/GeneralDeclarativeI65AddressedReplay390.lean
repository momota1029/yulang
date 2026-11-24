import Yulang.GeneralDeclarativeI65CanonicalReplay386

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree dictionaryForest)

mutual
/-- The actual dictionary constructors are paired against full
request occurrences. Every child is the same finite lowered child
of a source where request, not an unrelated event with the same key. -/
inductive AddressedDictionaryEvents [judgment : ReplayJudgment] (s : State) :
    Request → Dictionary → LiteralEventTree (s := s) → Prop where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩) :
      AddressedDictionaryForest s event.kids ds events →
      AddressedDictionaryEvents s q (.node event.declaration.id ds) (.node ⟨q,event⟩ events)

inductive AddressedDictionaryForest [judgment : ReplayJudgment] (s : State) :
    List Request → List Dictionary → LiteralEventForest (s := s) → Prop where
  | nil : AddressedDictionaryForest s [] [] .nil
  | cons :
      AddressedDictionaryEvents s q d first →
      AddressedDictionaryForest s qs ds rest →
      AddressedDictionaryForest s (q :: qs) (d :: ds) (.cons first rest)
end

section
variable [judgment : ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

/-- Addresses refine rather than replace the canonical diagnostic shape. -/
theorem addressed_replay_has_canonical_order
    {events : LiteralEventTree (s := s)}
    (addressed : AddressedDictionaryEvents s q d events) :
    ExactOrderedOccurrences (dictionaryTree d) events := by
  exact AddressedDictionaryEvents.rec
    (motive_1 := fun _ d events _ => ExactOrderedOccurrences (dictionaryTree d) events)
    (motive_2 := fun _ ds events _ => ExactOrderedForest (dictionaryForest ds) events)
    (fun {_ _ _} event _ _ below => by
      simpa only [dictionaryTree] using ExactOrderedOccurrences.node ⟨_,event⟩ below)
    (by simpa only [dictionaryForest] using (ExactOrderedForest.nil (s := s)))
    (fun _ _ first rest => by
      simpa only [dictionaryForest] using ExactOrderedForest.cons first rest)
    addressed

private theorem lower_ledger_exact_request_addresses
    {events : LiteralEventTree (s := s)} (matched : LoweredEventLedger s lowered events) :
    AddressedDictionaryEvents s q d events := by
  exact LoweredEventLedger.rec
    (motive_1 := fun {q d _} _ events _ => AddressedDictionaryEvents s q d events)
    (motive_2 := fun {qs ds _} _ events _ => AddressedDictionaryForest s qs ds events)
    (fun {_ _ _ _} event guard {_} _ kids => .node event guard kids)
    .nil
    (fun _ _ first rest => .cons first rest)
    matched

theorem exact_replay_ledger_addresses
    {replay : LiteralTreeFrom tree t lowered} {events : LiteralEventTree (s := s)}
    (eventMatch : ExactReplayEvents replay events) :
    AddressedDictionaryEvents s q d events :=
  lower_ledger_exact_request_addresses eventMatch.2

end
end Yulang.GeneralDeclarativeI65
