import Yulang.GeneralDeclarativeI65LiteralReplay386

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary Resolves Tree)
open GeneralDeclarativeWitnessTree349 (dictionaryTree)

mutual
/-- Every occurrence stays a node even when its own output list is
empty. The full event, not just its dictionary key, stays attached. -/
inductive LiteralEventTree {s : State} where
  | node : LiteralEvent s → LiteralEventForest (s := s) → LiteralEventTree (s := s)

inductive LiteralEventForest {s : State} where
  | nil : LiteralEventForest (s := s)
  | cons : LiteralEventTree (s := s) → LiteralEventForest (s := s) → LiteralEventForest (s := s)
end

mutual
def orderedLiteralReceipts {s : State} : LiteralEventTree (s := s) → List OrderedReceipt
  | .node event kids => event.2.receipts ++ orderedForestReceipts kids

def orderedForestReceipts {s : State} : LiteralEventForest (s := s) → List OrderedReceipt
  | .nil => []
  | .cons first rest => orderedLiteralReceipts first ++ orderedForestReceipts rest
end

mutual
/-- An event ledger is synchronized with the stored source event
and the exact where children at the matching constructor. -/
inductive SourceEventLedger (judgment : ReplayJudgment) (s : State) :
    {q : Request} → {t : Tree} → LiteralSourceTrace judgment s q t →
    LiteralEventTree (s := s) → Prop where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩)
      {sourceKids : LiteralSourceForest judgment s event.kids ts} :
      SourceForestLedger judgment s sourceKids events →
      SourceEventLedger judgment s (.selected ⟨q,event⟩ guard sourceKids) (.node ⟨q,event⟩ events)

inductive SourceForestLedger (judgment : ReplayJudgment) (s : State) :
    {qs : List Request} → {ts : List Tree} → LiteralSourceForest judgment s qs ts →
    LiteralEventForest (s := s) → Prop where
  | nil : SourceForestLedger judgment s .nil .nil
  | cons : SourceEventLedger judgment s head root → SourceForestLedger judgment s tail rest →
      SourceForestLedger judgment s (.cons head tail) (.cons root rest)
end

mutual
/-- Independently match that same ledger against the literal lowered
occurrences, including the actual source event at each node. -/
inductive LoweredEventLedger [judgment : ReplayJudgment] (s : State) :
    {q : Request} → {d : Dictionary} → {written : List OrderedReceipt} →
    GeneralTree s q d written → LiteralEventTree (s := s) → Prop where
  | node (event : LiteralLocalEvent s q)
      (guard : LiteralTraceRule judgment s q (.selected event.declaration.id event.kids) ⟨q,event⟩)
      {loweredKids : GeneralForest s event.kids ds later} :
      LoweredForestLedger s loweredKids events →
      LoweredEventLedger s (.node event guard loweredKids) (.node ⟨q,event⟩ events)

inductive LoweredForestLedger [judgment : ReplayJudgment] (s : State) :
    {qs : List Request} → {ds : List Dictionary} → {written : List OrderedReceipt} →
    GeneralForest s qs ds written → LiteralEventForest (s := s) → Prop where
  | nil : LoweredForestLedger s .nil .nil
  | cons : LoweredEventLedger s head root → LoweredForestLedger s tail rest →
      LoweredForestLedger s (.cons head tail) (.cons root rest)
end

mutual
/-- This projection checks the key and exact child order and
multiplicity separately from either proof of event identity. -/
inductive ExactOrderedOccurrences {s : State} : Tree → LiteralEventTree (s := s) → Prop where
  | node (event : LiteralEvent s) :
      ExactOrderedForest ts events →
      ExactOrderedOccurrences (.selected event.2.declaration.id ts) (.node event events)

inductive ExactOrderedForest {s : State} : List Tree → LiteralEventForest (s := s) → Prop where
  | nil : ExactOrderedForest [] .nil
  | cons : ExactOrderedOccurrences head event → ExactOrderedForest ts rest →
      ExactOrderedForest (head::ts) (.cons event rest)
end

section
variable [judgment : ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource (judgment := judgment) s) q t}
  {lowered : GeneralTree s q d written}

def ExactReplayEvents (replay : LiteralTreeFrom tree t lowered) (events : LiteralEventTree (s := s)) : Prop :=
  SourceEventLedger judgment s replay.source events ∧ LoweredEventLedger s lowered events

structure CanonicalDictionaryReplay
    (replay : LiteralTreeFrom tree t lowered) : Prop where
  ledger : ∃ events : LiteralEventTree,
    ExactReplayEvents replay events ∧
    ExactOrderedOccurrences (dictionaryTree d) events ∧
    orderedLiteralReceipts events = written

private theorem extract_paired_ledger
    {source : LiteralSourceTrace judgment s q t}
    (paired : LiteralReplayPair judgment s source lowered) :
    ∃ events : LiteralEventTree (s := s),
      SourceEventLedger judgment s source events ∧
      LoweredEventLedger s lowered events ∧
      ExactOrderedOccurrences t events ∧ orderedLiteralReceipts events = written := by
  exact LiteralReplayPair.rec
    (motive_1 := fun {_ t _ w} source lowered _ => ∃ events : LiteralEventTree (s := s),
      SourceEventLedger judgment s source events ∧
      LoweredEventLedger s lowered events ∧
      ExactOrderedOccurrences t events ∧ orderedLiteralReceipts events = w)
    (motive_2 := fun {_ ts _ w} source lowered _ => ∃ events : LiteralEventForest (s := s),
      SourceForestLedger judgment s source events ∧
      LoweredForestLedger s lowered events ∧
      ExactOrderedForest ts events ∧ orderedForestReceipts events = w)
    (fun {_q _ts _ds _later} event guard {_sourceKids _loweredKids} _pair tail => by
      obtain ⟨events,source,lowered,shape,rows⟩ := tail
      exact ⟨.node ⟨_,event⟩ events,.node event guard source,.node event guard lowered,
        .node ⟨_q,event⟩ shape,congrArg (event.receipts ++ ·) rows⟩)
    ⟨.nil,.nil,.nil,.nil,rfl⟩
    (fun _ _ left right => by
      obtain ⟨first,sourceL,loweredL,shapeL,rowsL⟩ := left
      obtain ⟨rest,sourceR,loweredR,shapeR,rowsR⟩ := right
      exact ⟨.cons first rest,.cons sourceL sourceR,.cons loweredL loweredR,
        .cons shapeL shapeR,by simp only [orderedForestReceipts,rowsL,rowsR]⟩)
    paired

theorem general_literal_replay_alignment
    (literal : t = dictionaryTree d) (replay : LiteralTreeFrom tree t lowered) :
    CanonicalDictionaryReplay replay := by
  obtain ⟨events,source,loweredMatch,shape,rows⟩ := extract_paired_ledger replay.paired
  exact ⟨⟨events,⟨source,loweredMatch⟩,literal ▸ shape,rows⟩⟩

end
end Yulang.GeneralDeclarativeI65
