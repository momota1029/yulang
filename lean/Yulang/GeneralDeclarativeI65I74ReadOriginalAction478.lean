import Yulang.GeneralDeclarativeI65I74OriginalPoseSegments478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarationPatterns (Pattern normalize)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose atSource)

structure ParsedAuthoredAction478 (p : Pattern) (word : List Pose) where
  action : Address
  segment : List Pose
  child : Pattern
  rest : List Pose
  real : WrittenPattern460.PhysicalOrigin.Origin p action segment child
  splitWord : segment ++ rest = word
  used : segment ≠ []

/-- Decode the next original action by reading the chosen written
pose in syntax. No compiled row, graph, policy or quoted action is
used. It rejects the old hidden-duplicate and distinct-join cases. -/
def parseNextAuthoredAction478 (p : Pattern) (word : List Pose) :
    Option (ParsedAuthoredAction478 p word) :=
  match p,word with
  | .app _ args,.app i::rest =>
    match found : args[i]? with
    | none => none
    | some child => some ⟨.arg i,[.app i],child,rest,.app found,rfl,by simp⟩
  | .record label value _,.payload::rest =>
    some ⟨.field label,[.payload],value,rest,.field,rfl,by simp⟩
  | .variant tag value,.variant::rest =>
    some ⟨.tag tag,[.variant],value,rest,.tag,rfl,by simp⟩
  | .record label _ tail,.tail::r => do
    let below ← parseNextAuthoredAction478 tail r
    match specific : below.action with
    | .field k =>
      if separate : label ≠ k then
        some ⟨.field k,.tail::below.segment,below.child,below.rest,
          .tail separate (specific ▸ below.real),by simp [below.splitWord],by simp⟩
      else none
    | _ => none
  | .join left right,.left::r =>
    if equal : normalize left = normalize right then do
      let below ← parseNextAuthoredAction478 left r
      pure ⟨below.action,.left::below.segment,below.child,below.rest,
        .left equal below.real,by simp [below.splitWord],by simp⟩
    else none
  | .join left right,.right::r =>
    if equal : normalize left = normalize right then do
      let below ← parseNextAuthoredAction478 right r
      pure ⟨below.action,.right::below.segment,below.child,below.rest,
        .right equal below.real,by simp [below.splitWord],by simp⟩
    else none
  | _,_ => none
termination_by word.length

theorem every_real_original_action_consumes_a_nonempty_pose478
    {p child : Pattern} {a : Address} {seg : List Pose}
    (old : WrittenPattern460.PhysicalOrigin.Origin p a seg child) :
    seg ≠ [] := by
  cases old <;> simp

theorem authentic_original_action_is_read_without_supplied_label478
    {p child : Pattern} {a : Address} {seg : List Pose}
    (old : WrittenPattern460.PhysicalOrigin.Origin p a seg child) (r : List Pose) :
    parseNextAuthoredAction478 p (seg++r) =
      some ⟨a,seg,child,r,old,rfl,every_real_original_action_consumes_a_nonempty_pose478 old⟩ := by
  induction old with
  | app yes =>
    simp only [List.singleton_append,parseNextAuthoredAction478]
    split
    · rename_i gone
      rw [yes] at gone
      contradiction
    · rename_i got found
      have same := Option.some.inj (found.symm.trans yes)
      subst got
      rfl
  | field => simp [parseNextAuthoredAction478]
  | tag => simp [parseNextAuthoredAction478]
  | tail different below ih =>
    simp [parseNextAuthoredAction478,different,ih,bind,Option.bind]
  | left same below ih =>
    simp [parseNextAuthoredAction478,same,ih,bind,Option.bind,pure]
  | right same below ih =>
    simp [parseNextAuthoredAction478,same,ih,bind,Option.bind,pure]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

