import Yulang.GeneralDictionaryBinderGap257
namespace Yulang.GeneralDictionaryHistoricalValues257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context atoms)
open GeneralDictionaryUpperHistory257 (history)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open CommonNominalFullCarrier

theorem raw_initial (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 have blockValid : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history n)) :=
   fun atom member => valid.2.2 atom (GeneralDictionaryUpperHistory257.block_in_source n member)
 have compact := (GeneralDictionaryCompactView257.recovered n assignment blockValid).mpr valid
 have small := (GeneralDictionaryFiveSlot257.models_exact n assignment).mp compact
 have small0 := (GeneralDictionaryNoModelRefinement257.all_iff_zero n assignment).mp small
 have compact0 := (GeneralDictionaryFiveSlot257.models_exact 0 assignment).mpr small0
 have raw0 := (GeneralDictionaryCompactView257.recovered 0 assignment (by intro atom member; cases member)).mp compact0
 rw [GeneralDictionaryLooseIterationBook240.context_zero] at raw0
 exact raw0

theorem atoms_mono (a b : Nat) (before : a ≤ b) : atoms a ⊆ atoms b := by
 induction before with
 | refl => exact fun _ h => h
 | @step b before ih => exact fun _ h => GeneralDictionaryReachableAggregate256.old_atoms b (ih h)

theorem lower_same (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment (lower index)).1 (assignment 2).1 :=
 GeneralDictionaryReachableAggregate256.lower_value index assignment
   (fun atom member => valid.2.2 atom (atoms_mono index n before member))

theorem upper_same (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment (upper index)).1 (assignment 4).1 := by
 have held : PresenceNormalForm.All model assignment
   (GeneralNominalAllocation.equations (upper index) (.inter (.var 4) (.var 4))) :=
   fun atom member => valid.2.2 atom (atoms_mono (index+1) n (by omega)
     (GeneralDictionaryUpperHistory257.upper_equations index member))
 have equation := (GeneralNominalCaptureMerges.equations_exact ..).mp held
 change Equivalent (assignment (upper index)).1 (.inter (assignment 4).1 (assignment 4).1) at equation
 have duplicate := GeneralPresenceIdempotentTree257.meet_self (assignment 4).1
 exact ⟨subtype_trans equation.1 duplicate.1,subtype_trans duplicate.2 equation.2⟩

theorem source_pair (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment 2).1 (assignment 4).1 := by
 have initial := raw_initial n assignment valid
 have lo := GeneralDictionaryLooseLoopInitial240.foo_fixed assignment initial
 have hi := GeneralDictionaryLooseLoopInitial240.foo4_fixed assignment initial
 exact ⟨subtype_trans lo.1 hi.2,subtype_trans hi.1 lo.2⟩
end Yulang.GeneralDictionaryHistoricalValues257
