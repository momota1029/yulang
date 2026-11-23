import Yulang.GeneralDeclarativeWitnessRecordResidual359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordWidthFixture359
open CommonNominalFullCarrier (Ty Equivalent Subtype record subtype_refl common_record_mono
 exactEmpty emptyRecord exactEmpty_below_width)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessRecordSpine359 (Spine)
open GeneralDeclarativeWitnessTwoSourcedEndpoints358 (left right)
open GeneralDeclarativeWitnessRecordResidual359 (Receipt Read lowerSpine upperSpine check after)
open GeneralDeclarativeWitnessRecordWindowFixture358 (payload integer_to_payload strict_original_payload_bounds)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)

def receipt : Receipt := ⟨⟨7,⟨60,61,62⟩,1,2,63,64⟩,
  .cons 9 1 0 (.terminal .exact),.cons 9 2 3 (.terminal .width)⟩
def authored : Source := ⟨(lowerSpine receipt).rows 60 ++ (upperSpine receipt).rows 62⟩
def current : State := ⟨⟨[left receipt.window,right receipt.window],[]⟩,authored.authored⟩

def lowRest : Ty := record 9 (.base .int) exactEmpty
def highRest : Ty := record 9 payload emptyRecord
def lowTy : Ty := record 7 (.base .int) lowRest
def highTy : Ty := record 7 payload highRest

def model (pickUpper : Bool) : Assignment := fun n => ((
  match n with
  | 0 => exactEmpty
  | 1 => .base .int
  | 2 => payload
  | 3 => emptyRecord
  | 60 => lowTy
  | 61 => if pickUpper then highTy else lowTy
  | 62 => highTy
  | 63 => lowRest
  | 64 => highRest
  | _ => .bottom),Common.rowEmpty)

theorem rests_ordered : Subtype lowRest highRest :=
  common_record_mono 9 integer_to_payload exactEmpty_below_width
theorem endpoints_ordered : Subtype lowTy highTy :=
  common_record_mono 7 integer_to_payload rests_ordered
theorem rests_not_reversible : ¬Subtype highRest lowRest := by
  intro rev
  exact strict_original_payload_bounds
    (GeneralNominalStructuralProjectionLaws.record_payload 9 payload (.base .int) emptyRecord exactEmpty rev)

theorem model_fits (pickUpper : Bool) : Models current (model pickUpper) := by
  refine ⟨⟨?_,fun _ bad => False.elim (List.not_mem_nil bad)⟩,?_⟩
  · intro atom member
    simp only [current,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> cases pickUpper
    · exact subtype_refl _
    · exact endpoints_ordered
    · exact endpoints_ordered
    · exact subtype_refl _
  · intro row member
    simp only [current,authored,lowerSpine,upperSpine,receipt,Spine.rows,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem read_checks : check authored current receipt = true := by decide +kernel

theorem current_without_center_equation : ∀ row ∈ current.equations, row.left ≠ 61 := by
  intro row member
  simp only [current,authored,lowerSpine,upperSpine,receipt,Spine.rows,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def wrongWidth : Receipt := {receipt with upper := .cons 9 2 3 (.terminal .exact)}
theorem cannot_collapse_width_to_exact : check authored current wrongWidth = false := by decide +kernel
theorem missing_authored_remainder_fails : check ⟨authored.authored.dropLast⟩ current receipt = false := by decide +kernel

theorem actual_window (pickUpper : Bool) :
    Subtype lowRest (subtract [7] (model pickUpper 61).1) ∧
    Subtype (subtract [7] (model pickUpper 61).1) highRest := by
  have read := GeneralDeclarativeWitnessRecordResidual359.check_exact.mp read_checks
  exact (GeneralDeclarativeWitnessRecordResidual359.authored_interval read _ (model_fits pickUpper)).2.2.2 [7]

theorem unlike_actual_remainders :
    Models current (model false) ∧ Models current (model true) ∧
    ¬ Equivalent (subtract [7] (model false 61).1) (subtract [7] (model true 61).1) :=
  ⟨model_fits false,model_fits true,fun same => rests_not_reversible same.2⟩

end Yulang.GeneralDeclarativeWitnessRecordWidthFixture359
