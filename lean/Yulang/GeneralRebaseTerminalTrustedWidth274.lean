import Yulang.GeneralRebaseTerminalMixedFrontier274
import Yulang.GeneralDictionaryVersionedTrusted233

set_option maxRecDepth 22000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralRebaseTerminalTrustedWidth274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVersionedSecondInstall233 (installed plan)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi)
open GeneralRebaseTerminalMixedRefresh274 (widthCandidates)
open GeneralRebaseTerminalRowFrame274 (oldPlan)
open GeneralNominalVersionedSupport233 (Trusted Fact SliceModels Readback)
open GeneralNominalVersionedMixedObservations233 (Justified)
open GeneralCanonicalObservations (Observation)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralRebaseCompoundOwnerCapture273 (PairFacts read_pair)

theorem old_readback : Readback installed [] oldPlan := by
 intro slot _ test observation head m model
 exact GeneralCanonicalObservations.recorded_sound _ m model.1 (GeneralNominalSupport.head_recorded head)

theorem older_trusted : Trusted installed [.input oldPlan] :=
 .input oldPlan .source GeneralDictionaryVersionedSecondInstall233.old_and_new.1 old_readback

theorem old_hi_width (m : Assignment) (valid : SliceModels installed [.input oldPlan] m) :
 Equivalent (m oldHi).1 .emptyRecord := by
 have inputs := valid.2.2 (.input oldPlan) List.mem_cons_self
 have equations := inputs.1.2.1
 rw [GeneralDictionaryOptionalInstall229.bindings_exact] at equations
 have pair : PairFacts m oldLo oldHi 4 2 := ((PresenceNormalForm.all_append ..).mp equations).1
 exact equivalent_trans (read_pair m oldLo oldHi 4 2 pair).2
   (GeneralDictionaryJournalRefinement228Source.width_two m valid.1)

def width (base : GeneralSourceState.State) (slot : Fin base.slots) : Observation :=
 .normalized base slot .emptyRecord

theorem width_justified (base : GeneralSourceState.State) (slot : Fin base.slots)
 (tracked : base.source slot ∈ widthCandidates) : Justified installed (width base slot) := by
 have possible := tracked
 simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at possible
 rcases possible with old | low | high
 · refine ⟨[],[.input oldPlan],.source,older_trusted,?_⟩
   intro m _ model
   change Equivalent (m (base.source slot)).1 .emptyRecord
   rw [old]
   exact old_hi_width m model
 · refine ⟨[],[.input plan],.source,GeneralDictionaryVersionedTrusted233.input_trusted,?_⟩
   intro m _ model
   change Equivalent (m (base.source slot)).1 .emptyRecord
   rw [low]
   exact (GeneralDictionaryVersionedTrusted233.aggregates model).1
 · refine ⟨[],[.input plan],.source,GeneralDictionaryVersionedTrusted233.input_trusted,?_⟩
   intro m _ model
   change Equivalent (m (base.source slot)).1 .emptyRecord
   rw [high]
   exact (GeneralDictionaryVersionedTrusted233.aggregates model).2

theorem legacy_cannot_justify_width (base : GeneralSourceState.State) (slot : Fin base.slots)
 (tracked : base.source slot ∈ widthCandidates) :
 ¬ ∃ facts, GeneralNominalCenteredHeadMatStepSupport.Trusted installed.legacy facts ∧
   ∀ m, GeneralNominalCenteredHeadMatStepSupport.Models installed.legacy facts m → (width base slot).Holds m := by
 rintro ⟨facts,trusted,sound⟩
 have satisfied := GeneralDictionaryVersionedSecondRefresh233.cut facts trusted
 have held := sound _ satisfied
 change Equivalent (GeneralDictionaryOptionalSource229.modelLow (base.source slot)).1 .emptyRecord at held
 have high : 4 < base.source slot := by
   simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at tracked
   rcases tracked with old | lo | hi <;> rw [‹base.source slot = _›] <;> decide +kernel
 have optional : (GeneralDictionaryOptionalSource229.modelLow (base.source slot)).1 =
   GeneralDictionaryOptionalOutput229.value := by
   have a : base.source slot ≠ 0 := by omega
   have b : base.source slot ≠ 1 := by omega
   have c : base.source slot ≠ 2 := by omega
   have d : base.source slot ≠ 3 := by omega
   simp [GeneralDictionaryOptionalSource229.modelLow,a,b,c,d]
   rfl
 rw [optional] at held
 exact GeneralDictionaryOptionalOutput229.not_width held

end Yulang.GeneralRebaseTerminalTrustedWidth274
