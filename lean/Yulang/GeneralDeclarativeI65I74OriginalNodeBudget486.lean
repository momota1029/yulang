import Yulang.GeneralDeclarativeI65I74ProducerTrail479

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460.PhysicalOrigin (Pose atSource sourceStep literal_occurrence)
open LiteralVisits473 (ReadStep StepWire)
open Producer479 (Site Trail)
open ObservationAlternatives473 (Positions)

mutual
def originalNodeBudget486 : Pattern → Nat
  | .var _ => 1
  | .app _ args => 1 + originalNodesBudget486 args
  | .record _ payload tail => 1 + originalNodeBudget486 payload + originalNodeBudget486 tail
  | .variant _ payload => 1 + originalNodeBudget486 payload
  | .join l r => 1 + originalNodeBudget486 l + originalNodeBudget486 r

def originalNodesBudget486 : List Pattern → Nat
  | [] => 0
  | a::as => originalNodeBudget486 a + originalNodesBudget486 as
end

private theorem an_original_argument_consumes_some_of_the_budget
    {child : Pattern} {args : List Pattern} (mem : child ∈ args) :
    originalNodeBudget486 child ≤ originalNodesBudget486 args := by
  induction args with
  | nil => cases mem
  | cons a as ih =>
    rcases List.mem_cons.mp mem with atHead|atTail
    · subst a
      rw [originalNodesBudget486]
      omega
    · have less := ih atTail
      rw [originalNodesBudget486]
      omega

private theorem literal_step_reduces_the_exact_original_size
    {p child : Pattern} {whereFrom : Pose} (atPlace : sourceStep p whereFrom = some child) :
    originalNodeBudget486 child < originalNodeBudget486 p := by
  cases p <;> cases whereFrom <;> simp only [sourceStep] at atPlace
  all_goals try contradiction
  all_goals try (have eq := Option.some.inj atPlace; subst child; simp only [originalNodeBudget486]; omega)
  rename_i key args index
  have inside := an_original_argument_consumes_some_of_the_budget (List.mem_of_getElem? atPlace)
  rw [originalNodeBudget486]
  omega

theorem following_written_locations_decreases_the_original_budget486
    {p child : Pattern} {poses : List Pose} (atPlace : atSource p poses = some child) :
    poses.length + originalNodeBudget486 child ≤ originalNodeBudget486 p := by
  induction poses generalizing p with
  | nil =>
    have same : p = child := Option.some.inj atPlace
    subst child
    simp
  | cons a as ih =>
    cases descends : sourceStep p a with
    | none => simp [atSource,descends] at atPlace
    | some next =>
      have step := literal_step_reduces_the_exact_original_size descends
      have later : atSource next as = some child := by simpa [atSource,descends] using atPlace
      have count := ih later
      simp only [List.length_cons]
      omega

private theorem chosen_real_origin_is_never_the_empty_path
    {p c : Pattern} {address poses} (o : WrittenPattern460.PhysicalOrigin.Origin p address poses c) :
    poses ≠ [] := by
  cases o <;> simp

theorem every_existing_finite_visit_stops_within_the_original_written_budget486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {first last : Site s pos} {moves points bit}
    (route : Trail s pos rel first moves points last bit) :
    moves.length + originalNodeBudget486 last.pattern ≤ originalNodeBudget486 first.pattern := by
  induction route with
  | stop => simp
  | step hop _ _ _ ih =>
    have actual := literal_occurrence hop.typed.writtenFrom
    have notEmpty := chosen_real_origin_is_never_the_empty_path hop.typed.writtenFrom
    have bound := following_written_locations_decreases_the_original_budget486 actual
    rw [hop.written] at bound
    have pos : 0 < List.length _ := List.length_pos_iff.mpr notEmpty
    simp only [List.length_cons]
    omega

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
