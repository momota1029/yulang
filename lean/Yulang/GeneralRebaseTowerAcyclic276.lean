import Yulang.GeneralRebaseTowerSemantics276

set_option maxRecDepth 22000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseTowerAcyclic276
open GeneralRebaseTowerSemantics276
open GeneralNominalOutputGrowth (tower)
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms (arity project)
variable {model : GeneralNominalCommonBridge.Assignment}

theorem edge_decreases (valid : GeneralNominalVersionedJournal232.Models state model)
    (source : ∀ identity, ∃ depth : Nat, (model identity).1 = tower depth)
    (edge : GeneralNominalVersionedCycles232.Edge state first last) : rank model last < rank model first := by
  obtain ⟨parent,test,index,_,one,two⟩ := edge
  have one := one model valid
  have two := two model valid
  obtain ⟨firstValue,seenFirst⟩ := one.1
  obtain ⟨firstForm,meaningFirst⟩ := observed_depth source seenFirst
  obtain ⟨projected,seenProjected⟩ := two.1
  have parentMeaning : ∀ value, Observes model parent value → Equivalent value (tower firstForm) := by
    intro value observed
    have same := one.2.2 firstValue value seenFirst observed
    exact ⟨subtype_trans same.2 meaningFirst.1,subtype_trans meaningFirst.2 same.1⟩
  obtain ⟨lastForm,smaller,meaningLast⟩ := GeneralRebaseTowerSemantics276.smaller firstForm parentMeaning test index seenProjected
  obtain ⟨lastValue,seenLast⟩ := two.2.1
  have equalLast := two.2.2 projected lastValue seenProjected seenLast
  have lastMeaning : Equivalent lastValue (tower lastForm) :=
    ⟨subtype_trans equalLast.2 meaningLast.1,subtype_trans meaningLast.2 equalLast.1⟩
  have uniqueFirst : GeneralNominalReadbackFunctionality.Unique model first := by
    obtain ⟨value,seen⟩ := one.2.1
    intro a b sa sb
    exact ⟨subtype_trans (one.2.2 a value sa seen).1 (one.2.2 b value sb seen).2,
      subtype_trans (one.2.2 b value sb seen).1 (one.2.2 a value sa seen).2⟩
  have uniqueLast : GeneralNominalReadbackFunctionality.Unique model last := by
    intro a b sa sb
    exact ⟨subtype_trans (two.2.2 projected a seenProjected sa).2 (two.2.2 projected b seenProjected sb).1,
      subtype_trans (two.2.2 projected b seenProjected sb).2 (two.2.2 projected a seenProjected sa).1⟩
  rw [rank_exact ⟨firstValue,seenFirst,meaningFirst⟩ uniqueFirst,
    rank_exact ⟨lastValue,seenLast,lastMeaning⟩ uniqueLast]
  exact smaller

theorem acyclic (valid : GeneralNominalVersionedJournal232.Models state model)
    (source : ∀ identity, ∃ depth : Nat, (model identity).1 = tower depth) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic state origin := by
  have paths : ∀ a b, GeneralNominalVersionedCycles232.Path state a b → rank model b ≤ rank model a := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_decreases valid source edge))
  rintro ⟨⟨next,edge,path⟩,_⟩
  have smaller := edge_decreases valid source edge
  have larger := paths _ _ path
  omega

end Yulang.GeneralRebaseTowerAcyclic276
