import Yulang.GeneralDictionaryUniformFill258
namespace Yulang.GeneralDictionaryUniformBlock258
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryUniformFill258 (fill)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryUpperHistory257 (history lowerEntry upperEntry)
open CommonNominalFullCarrier

theorem lower_equation (assignment : Assignment) (index : Nat) :
 All model (fill assignment) (GeneralNominalAllocation.equations (lower (index+1))
   (.union (.var (lower index)) (.var (lower index)))) := by
 apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
 change Equivalent (fill assignment (lower (index+1))).1
   (.union (fill assignment (lower index)).1 (fill assignment (lower index)).1)
 rw [GeneralDictionaryUniformFill258.lower_value,GeneralDictionaryUniformFill258.lower_value]
 have idem := GeneralPresenceSnapshotGrowth251.union_self (assignment 2).1
 exact ⟨idem.2,idem.1⟩

theorem upper_equation (assignment : Assignment) (index : Nat) :
 All model (fill assignment) (GeneralNominalAllocation.equations (upper index)
   (.inter (.var 4) (.var 4))) := by
 apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
 change Equivalent (fill assignment (upper index)).1
   (.inter (fill assignment 4).1 (fill assignment 4).1)
 rw [GeneralDictionaryUniformFill258.upper_value,GeneralDictionaryUniformFill258.initial assignment 4 (by decide)]
 have idem := GeneralPresenceIdempotentTree257.meet_self (assignment 4).1
 exact ⟨idem.2,idem.1⟩

/-- Every stage's actual historical block is satisfied by the SAME assignment
transform; the function does not consume the growing historical list. -/
theorem all_blocks (assignment : Assignment) (n : Nat) :
 All model (fill assignment) (GeneralPresenceDefinitionRewrite244.block (history n)) := by
 induction n with
 | zero => intro atom member; cases member
 | succ n ih =>
   change All model (fill assignment) ((history n ++ [lowerEntry n,upperEntry n]).flatMap _)
   rw [List.flatMap_append]
   apply (all_append ..).mpr
   constructor
   · exact ih
   · change All model (fill assignment)
       (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
         (GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)) ++ []))
     rw [List.append_nil]
     exact (all_append ..).mpr ⟨lower_equation assignment n,upper_equation assignment n⟩
end Yulang.GeneralDictionaryUniformBlock258
