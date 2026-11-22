import Yulang.GeneralDeclarativeWitnessExactRest349
import Yulang.GeneralDeclarativeWitnessRecordFixture349

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17500
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeWitnessExactRestFixture349
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeWitnessExactRest349 (Wire check checkList same_model)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeWitnessRecordFixture349 (center current)
open GeneralDeclarativeEndpointCase336 (rowLo endCode)
open GeneralDeclarativeEndpointMixedTail336 (rowHi width)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open CommonNominalFullCarrier (exactEmpty emptyRecord subtype_trans subtype_refl)
open GeneralDeclarativeRecordSplit330 (interval)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)

def lo : Equation := ⟨20,endCode⟩
def mid : Equation := ⟨21,endCode⟩
def high : Equation := ⟨22,width⟩
def state : State := appendFacts current [lo,mid,high]
def entry : Entry := ⟨.rest arg [7] endCode width,⟨20,21,22⟩⟩
def witness : Wire := ⟨[(7,.variable 4)],endCode,.currentRow 2,.currentRow 3,.currentRow 4,.currentRow 5⟩

theorem accepted : checkList state [entry] [witness] = true := by decide +kernel

theorem substituted_endpoint : check state entry {witness with centerShape := .currentRow 0} = false := by
  decide +kernel

theorem changed_center_slot : check state (entry.1,⟨20,23,22⟩) witness = false := by
  decide +kernel

def witnessModel : Assignment := fun n =>
  if n = 20 ∨ n = 21 then (exactEmpty,Common.rowEmpty)
  else if n = 22 then (emptyRecord,Common.rowEmpty)
  else GeneralDeclarativeWitnessRecordFixture349.model n

theorem state_model : Models state witnessModel := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e here
    change e ∈ [(0,1),(1,2)] at here
    rcases List.mem_cons.mp here with rfl|last
    · exact subtype_trans (interval 7).1 (interval 7).2
    · cases List.mem_singleton.mp last
      exact CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _) CommonNominalFullCarrier.exactEmpty_below_width
  · intro row h
    change row ∈ [rowLo,rowHi,center,lo,mid,high] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem nonvacuous : ModelsExact state [entry] witnessModel :=
  same_model accepted _ state_model

end Yulang.GeneralDeclarativeWitnessExactRestFixture349
