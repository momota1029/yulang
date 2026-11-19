import Yulang.GeneralRebaseTerminalFirstExact274

set_option maxRecDepth 17000
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTerminalActivation274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi)
open GeneralRebaseTerminalPublic274 (first)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralRebaseTerminalFirstExact274 (OldFacts)
open GeneralRebaseTerminalRows274 (HasLeaf before_models)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseTerminalRepair274 (repair repairs)
open GeneralRebaseTerminalStableCells274 (stable stable_terminal stable_store StoreChecked public_preserved)

def activeWrites : List Nat := [4,oldLo,oldHi,actual]

def activate (m : Assignment) : Assignment :=
 fun id => (if id = 4 ∨ id = oldLo then GeneralDictionaryOptionalOutput229.value
   else if id = oldHi ∨ id = actual then (m 2).1 else (m id).1,(m id).2)

theorem changes_only (m : Assignment) (id : Nat) (outside : id ∉ activeWrites) :
 activate m id = m id := by
 have h : id ≠ 4 ∧ id ≠ oldLo ∧ id ≠ oldHi ∧ id ≠ actual := by
   simpa [activeWrites] using outside
 simp [activate,h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem fixed_prefix (m : Assignment) (id : Nat) (small : id < 4) : activate m id = m id := by
 apply changes_only
 simp only [activeWrites,List.mem_cons,List.not_mem_nil,or_false,not_or]
 have loBig : 4 < oldLo := by decide +kernel
 have hiBig : 4 < oldHi := by decide +kernel
 have actualBig : 4 < actual := by decide +kernel
 exact ⟨by omega,by omega,by omega,by omega⟩

theorem output (m : Assignment) : (activate m 4).1 = GeneralDictionaryOptionalOutput229.value := rfl

theorem old_facts (m : Assignment) : OldFacts (activate m) := by
 have lower : (activate m oldLo).1 = GeneralDictionaryOptionalOutput229.value := rfl
 have upper : (activate m oldHi).1 = (m 2).1 := rfl
 have center : (activate m actual).1 = (m 2).1 := rfl
 unfold OldFacts
 rw [lower,output,upper,center,fixed_prefix m 2 (by decide)]
 exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩,subtype_refl _,subtype_refl _⟩

theorem initial_persists (m : Assignment) (source : Models before m) : Models before (activate m) := by
 have pub := (before_models _).mp source
 apply (before_models _).mpr
 refine ⟨fun i h => ?_,?_⟩
 · rw [fixed_prefix m i h]
   exact pub.1 i h
 · rw [output,fixed_prefix m 2 (by decide)]
   have width : Equivalent (m 2).1 .emptyRecord := pub.1 2 (by decide)
   exact subtype_trans GeneralDictionaryOptionalOutput229.below_width width.2

theorem checked_first (m : Assignment) (source : Models before m) : Models first (activate m) :=
 (GeneralRebaseTerminalFirstExact274.initial_to_first _).mpr
  ⟨initial_persists m source,by unfold Body; rw [output]; exact ⟨subtype_refl _,subtype_refl _⟩,old_facts m⟩

theorem checked_point (m : Assignment) (source : Models before m) : Models point (activate m) :=
 (GeneralDictionaryVersionedPointStage233.models_iff _).mpr (checked_first m source)

noncomputable def finish (m : Assignment) : Assignment := stable (repair (activate m))

theorem finished (m : Assignment) (source : Models before m) :
 Models installed (finish m) ∧ HasLeaf (finish m) ∧ StoreChecked (finish m) := by
 have full := stable_terminal _ (repairs (activate m) (checked_point m source))
 exact ⟨full,GeneralDictionaryVersionedSecondInstall233.evidence full,stable_store _ full⟩

theorem finish_public (m : Assignment) :
 (∀ id < 4, finish m id = m id) ∧
 (finish m 4).1 = GeneralDictionaryOptionalOutput229.value ∧
 (∀ id, (finish m id).2 = (m id).2) := by
 have cleanup : Agrees (repair (activate m)) (activate m) := GeneralRebaseTerminalRepair274.public_preserved _ _ _
 have complete : Agrees (finish m) (activate m) :=
   GeneralRebaseTerminalStableCells274.agrees_trans (public_preserved _) cleanup
 refine ⟨fun i h => (complete.1 i (by omega)).trans (fixed_prefix m i h),?_,fun i => complete.2 i⟩
 rw [complete.1 4 (by decide)]
 exact output m

end Yulang.GeneralRebaseTerminalActivation274
