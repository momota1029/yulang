import Yulang.GeneralDictionaryDirectView258
namespace Yulang.GeneralDictionaryInitialFill258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralDictionaryUniformFill258 (fill)
open GeneralDictionaryFiveSlot257 (view)
open CommonNominalFullCarrier

/-- Fill the unconstrained internal binder before uniform endpoint extension.
Unlike UniformFill258 this intentionally does NOT fix the old binder value. -/
def bind (assignment : Assignment) : Assignment :=
 GeneralPresenceOrderedBlock247.put model assignment actual (assignment 2).1

def complete (assignment : Assignment) : Assignment := fill (bind assignment)

theorem rows (assignment : Assignment) (name : Nat) : (bind assignment name).2 = (assignment name).2 :=
 GeneralPresenceOrderedBlock247.put_rows ..

theorem initial (assignment : Assignment) (name : Nat) (bound : name ≤ 4) : bind assignment name = assignment name := by
 apply GeneralPresenceOrderedBlock247.put_outside
 have above := GeneralDictionaryBinderGap257.actual_above
 omega

theorem binder (assignment : Assignment) : GeneralDictionaryBinderFact257.Holds (bind assignment) := by
 unfold GeneralDictionaryBinderFact257.Holds
 rw [initial assignment 2 (by decide)]
 change Equivalent (GeneralPresenceOrderedBlock247.put model assignment actual (assignment 2).1 actual).1 (assignment 2).1
 simp only [GeneralPresenceOrderedBlock247.put,ite_true]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem view_exact (n : Nat) (assignment : Assignment) :
 (view n).Models (bind assignment) ↔ (view n).Models assignment := by
 apply GeneralNominalViewSupport249.models_iff _ _ _ (rows assignment)
 intro name present
 exact congrArg Prod.fst (initial assignment name (GeneralDictionaryUniformView258.support_small n name present))

theorem raw_initial (assignment : Assignment) :
 (view 0).Models assignment ↔ GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 rw [← GeneralDictionaryFiveSlot257.models_exact]
 have raw := GeneralDictionaryCompactView257.recovered 0 assignment (by intro atom member; cases member)
 rw [GeneralDictionaryLooseIterationBook240.context_zero] at raw
 exact raw

theorem all_stages (assignment : Assignment) :
 (∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) (complete assignment)) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 rw [complete,GeneralDictionaryUniformJournal258.all_stages,GeneralDictionaryFiniteJournal257.models_exact]
 have held := binder assignment
 rw [and_iff_left held,view_exact,GeneralDictionaryNoModelRefinement257.all_iff_zero,raw_initial]

theorem public_agrees (assignment : Assignment) : GeneralDictionaryInitialProjection257.Agree (complete assignment) assignment := by
 constructor
 · intro name bound
   exact (GeneralDictionaryUniformFill258.initial (bind assignment) name bound).trans (initial assignment name bound)
 · intro name
   exact (GeneralDictionaryUniformFill258.rows (bind assignment) name).trans (rows assignment name)

theorem complete_binder (assignment : Assignment) :
 (complete assignment actual).1 = (assignment 2).1 := by
 rw [complete,GeneralDictionaryUniformFill258.actual_fixed]
 simp only [bind,GeneralPresenceOrderedBlock247.put,ite_true]
end Yulang.GeneralDictionaryInitialFill258
