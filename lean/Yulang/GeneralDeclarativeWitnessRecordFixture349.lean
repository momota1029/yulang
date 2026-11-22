import Yulang.GeneralDeclarativeWitnessRecord349
import Yulang.GeneralDeclarativeEndpointMixedTail336

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 6500000
namespace Yulang.GeneralDeclarativeWitnessRecordFixture349
open GeneralDeclarativeEndpointCase336 (rowLo endCode)
open GeneralDeclarativeEndpointMixedTail336 (rowHi width mixedModel strict)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached attach support cannot_promote)
open GeneralDeclarativeWitnessRecord349 (Wire check decode present)
open GeneralDeclarativeWitnessLiteral349 (eqExpr)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Subtype Equivalent exactEmpty emptyRecord subtype_trans subtype_refl record)
open GeneralDeclarativeRecordSplit330 (interval hi)

def center : Equation := ⟨1,.record 7 (.variable 4) endCode⟩
def current : State := ⟨⟨[],[(0,1),(1,2)]⟩,[rowLo,rowHi,center]⟩
def manifest : Manifest := ⟨[rowLo,rowHi]⟩

def actual : Attached current manifest :=
  ⟨fun _ next => List.mem_append_left [center] next⟩

def wire : Wire :=
  ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.inline 1 .same⟩

def full : Bool :=
  ((attach current manifest).map (fun a => check a arg [7] wire)).getD false

theorem independently_accepted : full = true := by decide +kernel

theorem literals :
    ((decode actual arg [7] wire).map fun r =>
      (eqExpr r.lowerEnd endCode,eqExpr r.upperEnd width)) = some (true,true) := by decide +kernel

theorem wrong_endpoint :
    check actual arg [7] {wire with upper := .inline 0 .same} = false := by decide +kernel

theorem wrong_path :
    check actual arg [7] {wire with bounds := ⟨.interval 1,.interval 0⟩} = false := by decide +kernel

theorem unknown_field : check actual arg [8] wire = false := by decide +kernel
theorem duplicate_field : check actual arg [7,7] wire = false := by decide +kernel

theorem ordinary_but_withheld :
    center ∈ current.equations ∧ center ∉ (restriction (support actual)).equations := by
  refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),cannot_promote actual ?_⟩
  intro member
  rcases List.mem_cons.mp member with one|other
  · have no : (1 : Nat) = 0 := congrArg Equation.left one
    cases no
  · have no : (1 : Nat) = 2 := congrArg Equation.left (List.mem_singleton.mp other)
    cases no

def model : Assignment := fun n => if n = 1 then (hi 7,Common.rowEmpty) else mixedModel n

theorem current_model : Models current model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e atSlot
    change e ∈ [(0,1),(1,2)] at atSlot
    rcases List.mem_cons.mp atSlot with rfl|last
    · exact subtype_trans (interval 7).1 (interval 7).2
    · cases List.mem_singleton.mp last
      exact CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _)
        CommonNominalFullCarrier.exactEmpty_below_width
  · intro e shown
    change e ∈ [rowLo,rowHi,center] at shown
    rcases List.mem_cons.mp shown with rfl|tail
    · exact eqv_refl _
    · rcases List.mem_cons.mp tail with rfl|other
      · exact eqv_refl _
      · cases List.mem_singleton.mp other
        exact eqv_refl _

theorem genuine_ends : ¬ Equivalent exactEmpty emptyRecord := by
  intro dropped
  exact strict [7] 8 (by decide)
    (GeneralDeclarativeEndpointRecord336.mask_below [7] dropped.2)

theorem nonvacuous :
    Models current model ∧
      ∃ w : GeneralDeclarativeWitnessRecord349.Checked actual arg [7],
        InInterval
          (GeneralDeclarativeEndpointRecord336.interp model
            (GeneralDeclarativeRecordResidual323.withTail
              (CommonRoleCanonicalRows.residual [7] (CommonRoleCanonicalRows.normalize w.lower)) w.lowerEnd))
          (GeneralDeclarativeEndpointRecord336.interp model
            (GeneralDeclarativeRecordResidual323.withTail
              (CommonRoleCanonicalRows.residual [7] (CommonRoleCanonicalRows.normalize w.upper)) w.upperEnd))
          (GeneralDeclarativeExactDelete337.subtract [7] (model arg.center).1) := by
  have good : check actual arg [7] wire = true := by decide +kernel
  obtain ⟨w⟩ := present good
  exact ⟨current_model,w,GeneralDeclarativeWitnessRecord349.residual_same_model w _ current_model⟩

end Yulang.GeneralDeclarativeWitnessRecordFixture349
