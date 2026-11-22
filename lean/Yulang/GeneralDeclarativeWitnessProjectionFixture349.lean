import Yulang.GeneralDeclarativeWitnessProjection349
import Yulang.GeneralDeclarativeWitnessRecordFixture349

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17500
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeWitnessProjectionFixture349
open GeneralDeclarativeWitnessManifest349 (Manifest attach Attached)
open GeneralDeclarativeWitnessRecord349 (Wire check)
open GeneralDeclarativeWitnessProjection349 (decode ordered replay_same_model)
open GeneralDeclarativeWitnessRecordFixture349 (center model)
open GeneralDeclarativeWitnessCutDecl334 (arg)
open GeneralDeclarativeEndpointCase336 (rowLo)
open GeneralDeclarativeEndpointMixedTail336 (width)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (emptyRecord subtype_trans subtype_refl)
open GeneralDeclarativeRecordSplit330 (interval)
open GeneralDeclarativeEndpointNames336 (Triple)

def upperPrefix : Equation := ⟨2,.record 7 (.variable 4) (.variable 13)⟩
def endRow : Equation := ⟨13,width⟩
def current : State := ⟨⟨[],[(0,1),(1,2)]⟩,[rowLo,upperPrefix,endRow,center]⟩
def manifest : Manifest := ⟨[rowLo,upperPrefix,endRow]⟩
def attached : Attached current manifest := ⟨fun _ h => List.mem_append_left [center] h⟩
def wire : Wire :=
  ⟨⟨.interval 0,.interval 1⟩,.inline 0 .same,.prefix 1 .same (.inline 2 .same)⟩

def realPattern : Pattern := .record 7 (.var 31) (.var 31)

theorem checked_named_tail :
    ((attach current manifest).map fun a =>
      (decode a arg realPattern wire).isSome).getD false = true := by decide +kernel

def incomplete : Manifest := ⟨[rowLo,upperPrefix]⟩

/-- The missing manifest row still exists as ordinary information.
Knowing the current equation does not authorize traversing that tail. -/
theorem withheld_named_tail :
    ((attach current incomplete).map fun a =>
      (decode a arg realPattern wire).isSome).getD false = false := by decide +kernel

theorem wrong_pattern :
    (decode attached arg (.record 8 (.var 31) (.var 31)) wire).isSome = false := by decide +kernel

theorem output_order {a : GeneralDeclarativeWitnessProjection349.Checked attached arg realPattern} :
    a.jobs.map Prod.fst = [31,31] := ordered a

def assignment : Assignment := fun n => if n = 13 then (emptyRecord,Common.rowEmpty) else model n

theorem current_model : Models current assignment := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair h
    change pair ∈ [(0,1),(1,2)] at h
    rcases List.mem_cons.mp h with rfl|last
    · exact subtype_trans (interval 7).1 (interval 7).2
    · cases List.mem_singleton.mp last
      exact CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _) CommonNominalFullCarrier.exactEmpty_below_width
  · intro e h
    change e ∈ [rowLo,upperPrefix,endRow,center] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem actual_projections :
    Models current assignment ∧
      ∃ a : GeneralDeclarativeWitnessProjection349.Checked attached arg realPattern,
        a.jobs.map Prod.fst = [31,31] ∧ ∀ job ∈ a.jobs, ∃ t : Triple,
          GeneralDeclarativeExactOverlay337.eval job.2 assignment = some t ∧ InInterval t.1 t.2.2 t.2.1 := by
  have ok : (decode attached arg realPattern wire).isSome = true := by decide +kernel
  cases chosen : decode attached arg realPattern wire with
  | none => simp [chosen] at ok
  | some a =>
    exact ⟨current_model,a,output_order,replay_same_model a _ current_model⟩

end Yulang.GeneralDeclarativeWitnessProjectionFixture349
