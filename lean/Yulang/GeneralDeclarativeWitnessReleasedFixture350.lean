import Yulang.GeneralDeclarativeWitnessReleased350
import Yulang.GeneralDeclarativeWitnessRecordFixture349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReleasedFixture350
open GeneralDeclarativeWitnessOrigins350 (Table attach Attached support)
open GeneralDeclarativeWitnessReleased350 (project)
open GeneralDeclarativeWitnessRecordFixture349 (center current model current_model wire)
open GeneralDeclarativeWitnessCutDecl334 (arg pat)
open GeneralDeclarativeEndpointCase336 (rowLo)
open GeneralDeclarativeEndpointMixedTail336 (rowHi)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralDeclarativeWhere319 (InInterval)

def withheld : Table := ⟨[rowLo],[(rowHi,9)],[]⟩
def completed : Table := {withheld with released := [9]}

def canRead (t : Table) : Bool :=
  ((attach current t).map fun a => (project a arg pat wire).isSome).getD false

theorem unfinished_is_not_read :
    canRead withheld = false := by decide +kernel

theorem another_release_is_not_this_release :
    canRead {withheld with released := [8]} = false := by decide +kernel

theorem exact_release_enables_read :
    canRead completed = true := by decide +kernel

theorem not_promoted_to_source :
    ¬ GeneralDeclarativeWitnessOrigins350.origin completed rowHi .source := by
  intro row
  have point : rowHi = rowLo := List.mem_singleton.mp row
  cases point

/-- The same ordinary current assignment works before and after the
authoritative release changes; only source eligibility changes. -/
theorem nonvacuous :
    Models current model ∧
    ∃ (a : Attached current completed) (r : GeneralDeclarativeWitnessReleased350.Checked a arg pat),
      ∀ job ∈ r.jobs, ∃ t : Triple,
        GeneralDeclarativeExactOverlay337.eval job.2 model = some t ∧ InInterval t.1 t.2.2 t.2.1 := by
  have ok := exact_release_enables_read
  unfold canRead at ok
  cases attached : attach current completed with
  | none => simp [attached] at ok
  | some a =>
    cases chosen : project a arg pat wire with
    | none => simp [attached,chosen] at ok
    | some ready =>
      exact ⟨current_model,a,ready,
        GeneralDeclarativeExactOverlay337.list_sound ready.actual ready.computed model current_model⟩

end Yulang.GeneralDeclarativeWitnessReleasedFixture350
