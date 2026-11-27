import Yulang.GeneralDeclarativeI65I74LiteralCapturePullback466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466LiteralCapturePullback
open Yulang.GeneralDeclarationPatterns (Pattern normalize normalizeArgs hide covered coveredArgs)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource sourceStep Pose)
/-- Reverse the very same `hide` renumbering. An address entering a
shadowed payload has no forward image. -/
def foldHide (k : Nat) (p : Pattern) (as : List Pose) : Option (List Pose) :=
  match p with
  | .record label _ tail =>
    if k = label then
      match as with
      | .tail::rest => foldHide k tail rest
      | _ => none
    else
      match as with
      | [] => some []
      | .payload :: rest => some (.payload :: rest)
      | .tail :: rest => (foldHide k tail rest).map (.tail :: ·)
      | _ => none
  | _ => some as

theorem hide_roundtrip_keeps_the_same_pre_normalized_occurrence
    (k : Nat) (p : Pattern) (after before : List Pose)
    (mapped : throughHide k p after = some before) : foldHide k p before = some after := by
  cases p with
  | var | app | variant | join =>
    cases Option.some.inj mapped
    rfl
  | record label value tail =>
    by_cases same : k = label
    · subst label
      have read : (throughHide k tail after).map (.tail :: ·) = some before := by
        simpa only [throughHide,ite_true] using mapped
      obtain ⟨loc,inside,rfl⟩ := Option.map_eq_some_iff.mp read
      simpa only [foldHide,ite_true] using
        hide_roundtrip_keeps_the_same_pre_normalized_occurrence k tail after loc inside
    · cases after with
      | nil =>
        simp [throughHide,same] at mapped
        subst before
        simp [foldHide,same]
      | cons a rest =>
        cases a with
        | payload =>
          simp [throughHide,same] at mapped
          subst before
          simp [foldHide,same]
        | tail =>
          have read : (throughHide k tail rest).map (.tail :: ·) = some before := by
            simpa only [throughHide,same,ite_false] using mapped
          obtain ⟨loc,inside,rfl⟩ := Option.map_eq_some_iff.mp read
          simp [foldHide,same,
            hide_roundtrip_keeps_the_same_pre_normalized_occurrence k tail rest loc inside]
        | app | variant | left | right =>
          simp [throughHide,same] at mapped

mutual
def pushPos : Pattern → List Pose → Option (List Pose)
  | _, [] => some []
  | .record _ payload _, .payload::rest => (pushPos payload rest).map (.payload :: ·)
  | .record tag _ tail, .tail::rest => do
    let normalized ← pushPos tail rest
    let filtered ← foldHide tag (normalize tail) normalized
    pure (.tail::filtered)
  | .variant _ payload, .variant::rest => (pushPos payload rest).map (.variant :: ·)
  | .app _ ps, .app i::rest => (pushArgs ps i rest).map (.app i :: ·)
  | _, _ => none
termination_by p _ => sizeOf p

def pushArgs : List Pattern → Nat → List Pose → Option (List Pose)
  | [], _, _ => none
  | p::_, 0, rest => pushPos p rest
  | _::ps, j+1, rest => pushArgs ps j rest
termination_by ps _ _ => sizeOf ps
end

mutual
theorem source_pose_rebase_is_a_left_inverse_to_the_same_pose
    (p : Pattern) (normalized orig : List Pose)
    (said : pullPos p normalized = some orig) : pushPos p orig = some normalized := by
  cases normalized with
  | nil =>
    simp [pullPos] at said
    subst orig
    simp [pushPos]
  | cons a rest =>
    cases p <;> cases a <;> try solve | simp [pullPos] at said
    case app.app key ps i =>
      have atArg : (pullArgs ps i rest).map (.app i :: ·) = some orig := by
        simpa only [pullPos] using said
      obtain ⟨input,found,rfl⟩ := Option.map_eq_some_iff.mp atArg
      simp [pushPos,source_args_rebase_left_inverse ps i rest input found]
    case record.payload k child tail =>
      have nested : (pullPos child rest).map (.payload :: ·) = some orig := by
        simpa only [pullPos] using said
      obtain ⟨input,found,rfl⟩ := Option.map_eq_some_iff.mp nested
      simp [pushPos,source_pose_rebase_is_a_left_inverse_to_the_same_pose child rest input found]
    case record.tail tag child tail =>
      cases cross : throughHide tag (normalize tail) rest with
      | none => simp [pullPos,cross,Option.bind] at said
      | some rawNext =>
        cases next : pullPos tail rawNext with
        | none => simp [pullPos,cross,next,Option.bind] at said
        | some inside =>
          have eq : .tail::inside = orig := by simpa [pullPos,cross,next,Option.bind] using said
          subst orig
          simp [pushPos,source_pose_rebase_is_a_left_inverse_to_the_same_pose tail rawNext inside next,
            hide_roundtrip_keeps_the_same_pre_normalized_occurrence tag (normalize tail) rest rawNext cross,
            Option.bind]
    case variant.variant key child =>
      have nested : (pullPos child rest).map (.variant :: ·) = some orig := by
        simpa only [pullPos] using said
      obtain ⟨input,found,rfl⟩ := Option.map_eq_some_iff.mp nested
      simp [pushPos,source_pose_rebase_is_a_left_inverse_to_the_same_pose child rest input found]
termination_by sizeOf p

theorem source_args_rebase_left_inverse
    (ps : List Pattern) (i : Nat) (normalized orig : List Pose)
    (said : pullArgs ps i normalized = some orig) : pushArgs ps i orig = some normalized := by
  cases ps with
  | nil => simp [pullArgs] at said
  | cons p ps =>
    cases i with
    | zero =>
      simpa only [pushArgs] using source_pose_rebase_is_a_left_inverse_to_the_same_pose p normalized orig
        (by simpa only [pullArgs] using said)
    | succ i =>
      simpa only [pushArgs] using source_args_rebase_left_inverse ps i normalized orig
        (by simpa only [pullArgs] using said)
termination_by sizeOf ps
end

theorem two_distinct_retained_binder_poses_do_not_collapse_to_the_same_original
    {p : Pattern} {first last orig : List Pose}
    (a : pullPos p first = some orig) (b : pullPos p last = some orig) : first = last := by
  exact Option.some.inj ((source_pose_rebase_is_a_left_inverse_to_the_same_pose p first orig a).symm.trans
    (source_pose_rebase_is_a_left_inverse_to_the_same_pose p last orig b))


end Yulang.C466LiteralCapturePullback
