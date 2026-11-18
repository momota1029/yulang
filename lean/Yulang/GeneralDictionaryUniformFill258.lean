import Yulang.GeneralDictionaryFamilyRecognition258
namespace Yulang.GeneralDictionaryUniformFill258
open GeneralDictionaryFamilyRecognition258
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralNominalCommonBridge (Assignment)

/-- Stage-independent reconstruction by bounded numeric-name recognition.
This is not a bounded-cost solver or a finite old source-state representation. -/
def fill (assignment : Assignment) (name : Nat) :=
 if isLower name = true then ((assignment 2).1,(assignment name).2)
 else if isUpper name = true then ((assignment 4).1,(assignment name).2)
 else assignment name

theorem rows (assignment : Assignment) (name : Nat) : (fill assignment name).2 = (assignment name).2 := by
 unfold fill
 split <;> first | rfl | split <;> rfl

theorem initial (assignment : Assignment) (name : Nat) (bound : name ≤ 4) : fill assignment name = assignment name := by
 obtain ⟨lo,hi⟩ := small name bound
 simp only [fill,lo,hi,Bool.false_eq_true,ite_false]

theorem lower_value (assignment : Assignment) (index : Nat) :
 (fill assignment (lower index)).1 = (assignment 2).1 := by
 cases index with
 | zero => exact congrArg Prod.fst (initial assignment 2 (by decide))
 | succ index =>
   have yes := (lower_iff (lower (index+1))).mpr ⟨index,rfl⟩
   simp only [fill,yes,ite_true]

theorem upper_value (assignment : Assignment) (index : Nat) :
 (fill assignment (upper index)).1 = (assignment 4).1 := by
 have yes := (upper_iff (upper index)).mpr ⟨index,rfl⟩
 have no : isLower (upper index) ≠ true := fun low => disjoint _ ⟨low,yes⟩
 simp only [fill,no,Bool.false_eq_true,ite_false,yes,ite_true]

theorem actual_tags : isLower actual = false ∧ isUpper actual = false := by
 constructor
 · apply Bool.eq_false_iff.mpr
   intro yes
   obtain ⟨index,equal⟩ := (lower_iff actual).mp yes
   exact GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 0 0 _ 0 0 8 0 equal
 · apply Bool.eq_false_iff.mpr
   intro yes
   obtain ⟨index,equal⟩ := (upper_iff actual).mp yes
   exact GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 1 0 _ 0 0 8 0 equal

theorem actual_fixed (assignment : Assignment) : fill assignment actual = assignment actual := by
 obtain ⟨lo,hi⟩ := actual_tags
 simp only [fill,lo,hi,Bool.false_eq_true,ite_false]

theorem outside (assignment : Assignment) (name : Nat)
 (lo : ∀ index, lower (index+1) ≠ name) (hi : ∀ index, upper index ≠ name) :
 fill assignment name = assignment name := by
 have noLo : isLower name ≠ true := by intro yes; obtain ⟨i,h⟩ := (lower_iff name).mp yes; exact lo i h
 have noHi : isUpper name ≠ true := by intro yes; obtain ⟨i,h⟩ := (upper_iff name).mp yes; exact hi i h
 simp only [fill,noLo,noHi,Bool.false_eq_true,ite_false]

theorem idempotent (assignment : Assignment) : fill (fill assignment) = fill assignment := by
 funext name
 have two := initial assignment 2 (by decide)
 have four := initial assignment 4 (by decide)
 change (if isLower name = true then ((fill assignment 2).1,(fill assignment name).2)
   else if isUpper name = true then ((fill assignment 4).1,(fill assignment name).2)
   else fill assignment name) = fill assignment name
 rw [two,four,rows]
 unfold fill
 split <;> first | rfl | split <;> rfl

theorem agrees (assignment : Assignment) : GeneralDictionaryFiniteJournal257.Agree (fill assignment) assignment := by
 constructor
 · intro name kept
   rcases kept with small | rfl
   · exact initial assignment name small
   · exact actual_fixed assignment
 · exact rows assignment
end Yulang.GeneralDictionaryUniformFill258
