import Yulang.GeneralDeclarativeI65I74ReadOriginalAction478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose)

structure ParsedAuthoredPath478 (p : Pattern) (literal : List Pose) where
  actions : List Address
  segments : List (List Pose)
  last : Pattern
  trail : WrittenActionTrail478 p actions segments last
  exact : segments.flatten = literal

def parseOriginalActionPath478 (p : Pattern) (literal : List Pose) :
    Option (ParsedAuthoredPath478 p literal) :=
  if empty : literal = [] then
    some ⟨[],[],p,.stop,empty.symm⟩
  else do
    let one ← parseNextAuthoredAction478 p literal
    have small : one.rest.length < literal.length := by
      have sum := congrArg List.length one.splitWord
      rw [List.length_append] at sum
      have positive : 0 < one.segment.length := by
        cases h : one.segment with
        | nil => exact (one.used h).elim
        | cons => simp
      omega
    let later ← parseOriginalActionPath478 one.child one.rest
    pure ⟨one.action::later.actions,one.segment::later.segments,later.last,
      .step one.real later.trail,by simp only [List.flatten_cons,later.exact,one.splitWord]⟩
termination_by literal.length

theorem literal_full_pose_reads_all_old_actions_and_segments478
    {p : Pattern} {actions : List Address} {parts : List (List Pose)} {last : Pattern}
    (old : WrittenActionTrail478 p actions parts last) :
    parseOriginalActionPath478 p parts.flatten = some ⟨actions,parts,last,old,rfl⟩ := by
  induction old with
  | stop =>
    rw [parseOriginalActionPath478]
    rfl
  | @step p a pose child rest pieces terminal first later ih =>
    have len : pose ++ pieces.flatten ≠ [] := by
      intro no
      have both := List.append_eq_nil_iff.mp no
      exact every_real_original_action_consumes_a_nonempty_pose478 first both.1
    have one := authentic_original_action_is_read_without_supplied_label478 first pieces.flatten
    change parseOriginalActionPath478 p (pose ++ pieces.flatten) = _
    rw [parseOriginalActionPath478]
    simp only [len,dite_false,one,bind,Option.bind,ih,pure]

theorem one_literal_word_cannot_choose_two_different_actual_action_sequences478
    {p : Pattern} {actions moves : List Address} {parts slices : List (List Pose)}
    {last endAt : Pattern}
    (a : WrittenActionTrail478 p actions parts last)
    (b : WrittenActionTrail478 p moves slices endAt)
    (same : parts.flatten = slices.flatten) :
    actions = moves ∧ parts = slices ∧ last = endAt := by
  have x := congrArg (Option.map fun out => (out.actions,out.segments,out.last))
    (literal_full_pose_reads_all_old_actions_and_segments478 a)
  have y := congrArg (Option.map fun out => (out.actions,out.segments,out.last))
    (literal_full_pose_reads_all_old_actions_and_segments478 b)
  have base : (parseOriginalActionPath478 p parts.flatten).map (fun out => (out.actions,out.segments,out.last)) =
      (parseOriginalActionPath478 p slices.flatten).map (fun out => (out.actions,out.segments,out.last)) := by
    rw [same]
  have both := Option.some.inj (x.symm.trans (base.trans y))
  exact ⟨(Prod.mk.inj both).1,(Prod.mk.inj (Prod.mk.inj both).2).1,(Prod.mk.inj (Prod.mk.inj both).2).2⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

