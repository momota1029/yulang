import Yulang.GeneralDictionaryHistoricalValues257
namespace Yulang.GeneralDictionaryBinderFact257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context plan packet)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopPacket240 (actual)
open CommonNominalFullCarrier

/-- A fixed internal certificate fact, not a new public aggregate atom. -/
def facts : List (Atom Nat) := GeneralNominalAllocation.equations actual (.var 2)
def Holds (assignment : Assignment) : Prop := Equivalent (assignment actual).1 (assignment 2).1

theorem facts_exact (assignment : Assignment) : All model assignment facts ↔ Holds assignment :=
 GeneralNominalCaptureMerges.equations_exact ..

theorem fits_exact (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalCaptureMerges.Fits assignment (lower (index+1),upper index) (assignment actual).1 ↔ Holds assignment := by
 have lo := GeneralDictionaryHistoricalValues257.lower_same n (index+1) (by omega) assignment valid
 have hi := GeneralDictionaryHistoricalValues257.upper_same n index before assignment valid
 have same := GeneralDictionaryHistoricalValues257.source_pair n assignment valid
 constructor
 · intro fits
   exact ⟨subtype_trans fits.2 (subtype_trans hi.1 same.2),subtype_trans lo.2 fits.1⟩
 · intro binder
   exact ⟨subtype_trans lo.1 binder.2,subtype_trans binder.1 (subtype_trans same.1 hi.2)⟩

theorem all_past_fits (n : Nat) (positive : 0 < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 (∀ index, index < n → GeneralNominalCaptureMerges.Fits assignment
   (lower (index+1),upper index) (assignment actual).1) ↔ Holds assignment := by
 constructor
 · intro every; exact (fits_exact n 0 positive assignment valid).mp (every 0 positive)
 · intro binder index before; exact (fits_exact n index before assignment valid).mpr binder

theorem input_requires (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (input : GeneralNominalVersionedPlans231.Inputs (plan index) assignment) : Holds assignment := by
 have fits := GeneralNominalVersionedPlans231.shared_center input (name := 0)
   (Or.inl (by change 0 ∈ GeneralDictionaryLooseLoopSource240.declaration.inputNames; decide +kernel))
 rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryLooseFamilyFull240.binder_exact] at fits
 change GeneralNominalCaptureMerges.Fits assignment
   ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet index).bindings).inputs 0)
   (assignment actual).1 at fits
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact] at fits
 exact (fits_exact n index before assignment valid).mp fits

theorem journal_requires (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) assignment) : Holds assignment := by
 have raw := valid.1.1
 rw [(GeneralDictionaryLooseIterationIteration240.stages (n+1)).shape.current] at raw
 exact input_requires (n+1) 0 (by omega) assignment raw
   ((valid.2.1 (plan 0) ((GeneralDictionaryLooseIterationIteration240.stages (n+1)).recorded 0 (by omega))).2.1)

theorem excludes_gap (n : Nat) : ¬ Holds (GeneralDictionaryBinderGap257.witness (n+1)) := by
 intro binder
 have fit := (fits_exact (n+1) 0 (by omega) _ (GeneralDictionaryBinderGap257.raw_witness (n+1))).mpr binder
 have impossible := subtype_trans (GeneralDictionaryBinderGap257.lower_value (n+1) 1 (by omega)).2 fit.1
 rw [GeneralDictionaryBinderGap257.actual_bottom] at impossible
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl GeneralDictionaryLooseLoopSource240.S],rfl,(by
     intro depth
     apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
     intro rank env observation accepted
     exact CommonNominalFullDemand.probeAt_bottom rank observation),impossible⟩

theorem facts_length : facts.length = 2 := rfl
end Yulang.GeneralDictionaryBinderFact257
