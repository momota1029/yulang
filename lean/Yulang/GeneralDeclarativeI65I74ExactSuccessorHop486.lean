import Yulang.GeneralDeclarativeI65I74ProducerTrail479

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose exact_original_occurrences)
open LiteralVisits473 (StepWire)
open Producer479 (Site Hop readHop)
open ObservationAlternatives473 (Positions graphOf)
open CommonRoleRegularGraph (successors)

def possibleOriginalActions486 : Pattern → List Address
  | .var _ => []
  | .app _ args => (List.range args.length).map .arg
  | .record label _ tail => .field label :: possibleOriginalActions486 tail
  | .variant tag _ => [.tag tag]
  | .join l r => possibleOriginalActions486 l ++ possibleOriginalActions486 r

theorem every_written_child_uses_some_finite_original_action486
    {p x : Pattern} {a : Address} {path : List Pose}
    (written : WrittenPattern460.PhysicalOrigin.Origin p a path x) :
    a ∈ possibleOriginalActions486 p := by
  induction written with
  | app atArg =>
    exact List.mem_map.mpr ⟨_,List.mem_range.mpr (List.getElem?_eq_some_iff.mp atArg).1,rfl⟩
  | field => exact List.mem_cons_self ..
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih
  | tag => exact List.mem_cons_self ..
  | left _ _ ih => exact List.mem_append_left _ ih
  | right _ _ ih => exact List.mem_append_right _ ih

def possibleOriginalSteps486 (p : Pattern) : List StepWire :=
  (possibleOriginalActions486 p).flatMap fun a =>
    (WrittenPattern460.PhysicalOrigin.children p a).map (fun hit => ⟨a,hit.1⟩)

theorem every_actual_local_hop_has_its_exact_written_step_in_the_finite_original_list486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {here next : Site s pos} {w : StepWire}
    (move : Hop here next w) :
    w ∈ possibleOriginalSteps486 here.pattern := by
  have action := every_written_child_uses_some_finite_original_action486 move.typed.writtenFrom
  have spelled := (exact_original_occurrences ..).mpr move.typed.writtenFrom
  exact List.mem_flatMap.mpr ⟨w.action,action,List.mem_map.mpr ⟨_,spelled,by cases w; rfl⟩⟩

/-- Only the actual existing reader accepts a proposal from the finite list.
Enumeration itself grants no permission to use a candidate's visited site. -/
def finiteExistingHops486 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (here : Site s pos) : List (StepWire × Site s pos) :=
  (possibleOriginalSteps486 here.pattern).flatMap fun w =>
    (successors (graphOf s pos) here.index).filterMap fun idx => (readHop here w idx).map (fun arrived => (w,arrived))

theorem finite_hops_are_exact_existing_written_visits486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {here next : Site s pos} {w : StepWire} :
    (w,next) ∈ finiteExistingHops486 here ↔ Nonempty (Hop here next w) := by
  constructor
  · intro found
    obtain ⟨first,_,rest⟩ := List.mem_flatMap.mp found
    obtain ⟨i,_,trial⟩ := List.mem_filterMap.mp rest
    cases ran : readHop here first i with
    | none => simp [ran] at trial
    | some out =>
      have exact : (first,out) = (w,next) := Option.some.inj (by simpa [ran] using trial)
      cases exact
      exact (Producer479.reified_hop_keeps_the_same_old_place479 ran).2
  · rintro ⟨move⟩
    refine List.mem_flatMap.mpr
      ⟨w,every_actual_local_hop_has_its_exact_written_step_in_the_finite_original_list486 move,?_⟩
    exact List.mem_filterMap.mpr
      ⟨next.index,move.edge,by simp [Producer479.exact_hop_has_a_unique_replay479 move]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
