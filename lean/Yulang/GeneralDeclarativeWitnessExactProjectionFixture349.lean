import Yulang.GeneralDeclarativeWitnessExactProjection349
import Yulang.GeneralDeclarativeWitnessExactRestFixture349

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17500
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeWitnessExactProjectionFixture349
open GeneralDeclarativeWitnessExactRest349 (Wire)
open GeneralDeclarativeWitnessExactProjection349 (checkedList fixed_models)
open GeneralDeclarativeWitnessExactRestFixture349 (entry witness witnessModel lo mid high)
open GeneralDeclarativeWitnessRecordFixture349 (center)
open GeneralDeclarativeEndpointCase336 (rowLo endCode)
open GeneralDeclarativeEndpointMixedTail336 (rowHi)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeRecordSplit330 (interval)
open CommonNominalFullCarrier (subtype_trans subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)

def payloadLo : Equation := ⟨24,.variable 3⟩
def payloadMid : Equation := ⟨25,.variable 4⟩
def payloadHigh : Equation := ⟨26,.variable 4⟩

def state : State :=
  appendFacts GeneralDeclarativeWitnessExactRestFixture349.state [payloadLo,payloadMid,payloadHigh]

def captureField : Entry := ⟨.field arg 7 (.variable 3) (.variable 4),⟨24,25,26⟩⟩
def fieldProof : Wire := ⟨[(7,.variable 4)],endCode,.currentRow 2,.currentRow 6,.currentRow 7,.currentRow 8⟩

theorem both : checkedList state [captureField,entry] [fieldProof,witness] = true := by decide +kernel

theorem changed_order :
    checkedList state [captureField,entry] [witness,fieldProof] = false := by decide +kernel

theorem fake_middle :
    checkedList state [captureField,entry] [{fieldProof with middle := .currentRow 8},witness] = false := by decide +kernel

def model : Assignment := fun n =>
  if n = 24 then witnessModel 3
  else if n = 25 ∨ n = 26 then witnessModel 4
  else witnessModel n

theorem state_model : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e h
    change e ∈ [(0,1),(1,2)] at h
    rcases List.mem_cons.mp h with rfl|last
    · exact subtype_trans (interval 7).1 (interval 7).2
    · cases List.mem_singleton.mp last
      exact CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _) CommonNominalFullCarrier.exactEmpty_below_width
  · intro row h
    change row ∈ [rowLo,rowHi,center,lo,mid,high,payloadLo,payloadMid,payloadHigh] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem same_fixed_model : ModelsExact state [captureField,entry] model :=
  fixed_models both _ state_model

end Yulang.GeneralDeclarativeWitnessExactProjectionFixture349
