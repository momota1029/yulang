import Yulang.GeneralDeclarativeI65I74X6AmbiguousVisits417

namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.RawGraphAudit
open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeLowerKnown321 (alias_refl)
open Yulang.GeneralDeclarativeK2Graph321 (Shape)
open Yulang.GeneralDeclarativeK2Alias321 (AliasCycle)
open Yulang.GeneralDeclarativeGraphRows321 (observed structural literal_head)
open Yulang.GeneralDeclarativeInspect321 (Visit PatternK2)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410
  exact_escape_tracks_original_edge410)
open PlainMerged416 (variantRow416 idempotentRow)

def original : Equation := variantRow416 0 20 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[original,OpenTail414.intRow 1,idempotentRow 0]⟩
def loop (site : Nat) : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 site 20 site]}
def stopRoot : ExactEscapeWire := ⟨[0,1],[0,1]⟩
def offRoute : ExactEscapeWire := ⟨[0,1,2],[0,1,2]⟩
def stopPayload : ExactEscapeWire := ⟨[0,1,2],[2,0,2]⟩

theorem loop_is_actual_raw_cycle417 (site : Nat) :
    AliasCycle (loop site) (observed (loop site)) site := by
  have present : variantRow416 site 20 site ∈ (loop site).equations := by simp [loop]
  refine ⟨site,site,⟨.variant 20 site,literal_head present rfl,?_⟩,.refl _,alias_refl _⟩
  simp [Shape.children]

theorem actual_payload_cycle_survives_root_safety417 :
    ¬ AliasCycle (loop 1) (observed (loop 1)) 0 ∧
    PatternK2 (loop 1) 0 (groundCode 20) := by
  have goodRoot : checkExactEscape (loop 1) 0 stopRoot = true := by decide +kernel
  refine ⟨exact_escape_refutes_raw_root_K2410 goodRoot,1,?_,loop_is_actual_raw_cycle417 1⟩
  apply Visit.variant
  · exact literal_head (by simp [loop,ordinary,original] : original ∈ (loop 1).equations) rfl
  · exact .here .primitive

theorem actual_off_path_cycle_is_not_a_ground_visit417 :
    AliasCycle (loop 2) (observed (loop 2)) 2 ∧
    ¬ Visit (structural (loop 2)) 0 (groundCode 20) 2 := by
  have goodRoot : checkExactEscape (loop 2) 0 offRoute = true := by decide +kernel
  refine ⟨loop_is_actual_raw_cycle417 2,?_⟩
  intro accepted
  change Visit (structural (loop 2)) 0 (.variant 20 (.primitive (.scalar .int) [])) 2 at accepted
  cases accepted with
  | variant seen along =>
    rename_i child
    have fixed := scalar_int_has_no_descendant417 along
    have start : offRoute.side 0 ≤ 1 := by decide +kernel
    have visits := exact_escape_tracks_original_edge410 (b := child) goodRoot start
      ⟨.variant 20 _,seen,by simp [Shape.children]⟩
    rw [← fixed] at visits
    have different : offRoute.side 2 ≠ 1 := by decide +kernel
    exact different visits

theorem actual_off_path_cycle_does_not_block_either_gate417 :
    checkExactEscape (loop 2) 0 offRoute = true ∧
    checkExactEscape (loop 2) 1 stopPayload = true :=
  by decide +kernel

#print axioms loop_is_actual_raw_cycle417
#print axioms actual_payload_cycle_survives_root_safety417
#print axioms actual_off_path_cycle_is_not_a_ground_visit417
#print axioms actual_off_path_cycle_does_not_block_either_gate417
end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.RawGraphAudit
