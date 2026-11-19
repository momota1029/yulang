import Yulang.GeneralDictionaryHeadlessPreparation

namespace Yulang.GeneralRebaseOccurrenceEq267
open GeneralSourceState (Demand Output)
open GeneralSourceDictionaries (Occurrence)

local instance outputEq : DecidableEq Output := by
 intro first last
 cases first with | mk fn ft =>
   cases last with | mk ln lt =>
     exact decidable_of_iff (fn = ln ∧ ft = lt) (by simp)

def demandEq : DecidableEq (Demand roles) := by
 intro first last
 cases first with | mk fr fa fo fp =>
   cases last with | mk lr la lo lp =>
     by_cases sameRole : fr = lr
     · subst lr
       letI : Decidable (fa = la) := decidable_of_iff (∀ index, fa index = la index)
         ⟨fun pointwise => funext pointwise,fun same index => congrFun same index⟩
       exact decidable_of_iff (fa = la ∧ fo = lo) (by simp)
     · exact isFalse (by intro same; cases same; exact sameRole rfl)

def occurrenceEq : DecidableEq (Occurrence roles) := by
 letI : DecidableEq (Demand roles) := demandEq
 intro first last
 cases first with | mk fi fd =>
   cases last with | mk li ld =>
     exact decidable_of_iff (fi = li ∧ fd = ld) (by simp)

def same (first last : Occurrence roles) : Bool := @decide (first = last) (occurrenceEq first last)

theorem same_exact (first last : Occurrence roles) : same first last = true ↔ first = last := by
 unfold same
 simp

end Yulang.GeneralRebaseOccurrenceEq267
