import Yulang.GeneralDeclarativeI65CanonicalReplay386

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree)

section
variable [judgment : ReplayJudgment] {s : State}

mutual
/-- Meaning is indexed by the exact lowered tree rather than just by its
dictionary and flattened receipt list. P is a local, same-model predicate
to be supplied by the concrete I-65 semantics, never a classifier. -/
def TreeMeaningOver (P : LiteralEvent s → Prop) :
    {q : Request} → {d : Dictionary} → {written : List OrderedReceipt} →
    GeneralTree s q d written → Prop
  | q, _, _, .node event _ kids => P ⟨q,event⟩ ∧ ForestMeaningOver P kids

def ForestMeaningOver (P : LiteralEvent s → Prop) :
    {qs : List Request} → {ds : List Dictionary} → {written : List OrderedReceipt} →
    GeneralForest s qs ds written → Prop
  | _, _, _, .nil => True
  | _, _, _, .cons head tail => TreeMeaningOver P head ∧ ForestMeaningOver P tail
end

mutual
/-- Independent semantic predicate on the explicit canonical occurrence ledger.
Even a node with no output receipts retains a local semantic obligation. -/
def LedgerMeaning (P : LiteralEvent s → Prop) : LiteralEventTree (s := s) → Prop
  | .node event kids => P event ∧ LedgerForestMeaning P kids

def LedgerForestMeaning (P : LiteralEvent s → Prop) : LiteralEventForest (s := s) → Prop
  | .nil => True
  | .cons first rest => LedgerMeaning P first ∧ LedgerForestMeaning P rest
end

private theorem meaning_on_matched_ledger {P : LiteralEvent s → Prop}
    {q : Request} {d : Dictionary} {written : List OrderedReceipt}
    {lowered : GeneralTree s q d written} {events : LiteralEventTree (s := s)}
    (paired : LoweredEventLedger s lowered events) (meaning : TreeMeaningOver P lowered) :
    LedgerMeaning P events := by
  revert meaning
  exact LoweredEventLedger.rec
    (motive_1 := fun {_ _ _} lowered events _ => TreeMeaningOver P lowered → LedgerMeaning P events)
    (motive_2 := fun {_ _ _} lowered events _ => ForestMeaningOver P lowered → LedgerForestMeaning P events)
    (fun {_ _ _ _} _ _ {_} _ below meaning => by
      exact ⟨meaning.1, below meaning.2⟩)
    (fun _ => True.intro)
    (fun _ _ left right meaning => by
      exact ⟨left meaning.1, right meaning.2⟩)
    paired

variable {q : Request} {d : Dictionary} {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

theorem aligned_same_event_semantics {P : LiteralEvent s → Prop}
    {replay : LiteralTreeFrom tree t lowered}
    (alignment : CanonicalDictionaryReplay replay)
    (meaning : TreeMeaningOver P lowered) :
    ∃ events : LiteralEventTree (s := s),
      ExactReplayEvents replay events ∧
      ExactOrderedOccurrences (dictionaryTree d) events ∧
      orderedLiteralReceipts events = written ∧ LedgerMeaning P events := by
  obtain ⟨events, exactEvents, order, receipts⟩ := alignment.ledger
  exact ⟨events, exactEvents, order, receipts, meaning_on_matched_ledger exactEvents.2 meaning⟩

end
end Yulang.GeneralDeclarativeI65
