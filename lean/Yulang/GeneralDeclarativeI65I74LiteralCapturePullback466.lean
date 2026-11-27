import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466LiteralCapturePullback
open Yulang.GeneralDeclarationPatterns (Pattern normalize normalizeArgs hide covered coveredArgs)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource sourceStep Pose)

/-- Pull a literal address back through the existing hide operation.
A skipped shadow adds an original tail step without consuming a new pose. -/
def throughHide (k : Nat) (p : Pattern) (as : List Pose) : Option (List Pose) :=
  match p with
  | .record label _ tail =>
    if k = label then (throughHide k tail as).map (.tail :: ·)
    else
      match as with
      | [] => some []
      | .payload :: rest => some (.payload :: rest)
      | .tail :: rest => (throughHide k tail rest).map (.tail :: ·)
      | _ => none
  | _ => some as

theorem hide_pullback_preserves_the_actual_subtree
    (k : Nat) (p : Pattern) (as : List Pose) (out : Nat)
    (checked : atSource (hide k p) as = some (.var out)) :
    ∃ rooted, throughHide k p as = some rooted ∧ atSource p rooted = some (.var out) := by
  cases p with
  | var | app | variant | join => exact ⟨as,rfl,checked⟩
  | record label payload tail =>
    by_cases hid : k = label
    · subst label
      have onTail : atSource (hide k tail) as = some (.var out) := by simpa [hide] using checked
      obtain ⟨loc,read,selected⟩ := hide_pullback_preserves_the_actual_subtree k tail as out onTail
      exact ⟨.tail::loc,by simp [throughHide,read],selected⟩
    · cases as with
      | nil => simp [hide,hid,atSource] at checked
      | cons a rest =>
        cases a with
        | payload =>
          exact ⟨.payload::rest,by simp [throughHide,hid],by
            simpa [hide,hid,atSource,sourceStep,Option.bind] using checked⟩
        | tail =>
          have onTail : atSource (hide k tail) rest = some (.var out) := by
            simpa [hide,hid,atSource,sourceStep,Option.bind] using checked
          obtain ⟨loc,read,selected⟩ :=
            hide_pullback_preserves_the_actual_subtree k tail rest out onTail
          exact ⟨.tail::loc,by simp [throughHide,hid,read],selected⟩
        | app | left | right | variant =>
          simp [hide,hid,atSource,sourceStep,Option.bind] at checked


mutual
def pullPos : Pattern → List Pose → Option (List Pose)
  | _, [] => some []
  | .record _ payload _, .payload::rest => (pullPos payload rest).map (.payload :: ·)
  | .record tag _ tail, .tail::rest => do
    let root ← throughHide tag (normalize tail) rest
    let rooted ← pullPos tail root
    pure (.tail::rooted)
  | .variant _ payload, .variant::rest => (pullPos payload rest).map (.variant :: ·)
  | .app _ ps, .app i::rest => (pullArgs ps i rest).map (.app i :: ·)
  | _, _ => none
termination_by p _ => sizeOf p

def pullArgs : List Pattern → Nat → List Pose → Option (List Pose)
  | [], _, _ => none
  | p::_, 0, rest => pullPos p rest
  | _::ps, j+1, rest => pullArgs ps j rest
termination_by ps _ _ => sizeOf ps
end

mutual
theorem pull_joinfree_normalized_binder_to_exact_written_source
    (p : Pattern) (as : List Pose) (out : Nat)
    (good : covered p = true) (got : atSource (normalize p) as = some (.var out)) :
    ∃ orig, pullPos p as = some orig ∧ atSource p orig = some (.var out) := by
  cases p with
  | var n =>
    cases as with
    | nil => exact ⟨[],by simp [pullPos],got⟩
    | cons a rest => cases a <;> simp [normalize,atSource,sourceStep] at got
  | app k ps =>
    cases as with
    | nil => simp [normalize,atSource] at got
    | cons a rest =>
      cases a with
      | app i =>
        obtain ⟨loc,q,atArg,raw,sub⟩ :=
          pull_joinfree_argument_binder_to_exact_written_source ps i rest out good
            (by simpa [normalize,atSource,sourceStep] using got)
        exact ⟨.app i::loc,by simp [pullPos,raw],by simp [atSource,sourceStep,atArg,sub]⟩
      | payload | tail | variant | left | right => simp [normalize,atSource,sourceStep] at got
  | record k p tail =>
    have both : covered p = true ∧ covered tail = true := by simpa [covered] using good
    cases as with
    | nil => simp [normalize,atSource] at got
    | cons a rest =>
      cases a with
      | payload =>
        obtain ⟨loc,found,same⟩ := pull_joinfree_normalized_binder_to_exact_written_source p rest out both.1
          (by simpa [normalize,atSource,sourceStep] using got)
        exact ⟨.payload::loc,by simp [pullPos,found],same⟩
      | tail =>
        obtain ⟨edited,front,sub⟩ := hide_pullback_preserves_the_actual_subtree k (normalize tail) rest out
          (by simpa [normalize,atSource,sourceStep] using got)
        obtain ⟨loc,found,same⟩ := pull_joinfree_normalized_binder_to_exact_written_source tail edited out both.2 sub
        exact ⟨.tail::loc,by simp [pullPos,front,found],same⟩
      | app | variant | left | right => simp [normalize,atSource,sourceStep] at got
  | variant k p =>
    cases as with
    | nil => simp [normalize,atSource] at got
    | cons a rest =>
      cases a with
      | variant =>
        obtain ⟨loc,found,same⟩ := pull_joinfree_normalized_binder_to_exact_written_source p rest out good
          (by simpa [normalize,atSource,sourceStep] using got)
        exact ⟨.variant::loc,by simp [pullPos,found],same⟩
      | app | payload | tail | left | right => simp [normalize,atSource,sourceStep] at got
  | join _ _ => cases good
termination_by sizeOf p

theorem pull_joinfree_argument_binder_to_exact_written_source
    (ps : List Pattern) (i : Nat) (as : List Pose) (out : Nat)
    (good : coveredArgs ps = true)
    (got : ((normalizeArgs ps)[i]?).bind (fun p => atSource p as) = some (.var out)) :
    ∃ loc q, ps[i]? = some q ∧ pullArgs ps i as = some loc ∧
      atSource q loc = some (.var out) := by
  cases ps with
  | nil => simp [normalizeArgs] at got
  | cons p rest =>
    have both : covered p = true ∧ coveredArgs rest = true := by simpa [coveredArgs] using good
    cases i with
    | zero =>
      obtain ⟨loc,found,same⟩ := pull_joinfree_normalized_binder_to_exact_written_source p as out both.1
        (by simpa [normalizeArgs] using got)
      exact ⟨loc,p,rfl,(by simpa [pullArgs] using found),same⟩
    | succ i =>
      obtain ⟨loc,q,current,found,same⟩ := pull_joinfree_argument_binder_to_exact_written_source rest i as out both.2
        (by simpa [normalizeArgs] using got)
      exact ⟨loc,q,current,(by simpa [pullArgs] using found),same⟩
termination_by sizeOf ps
end


open Yulang.C466WrittenBinderCoordinates
open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.Checker408 (Problem)
open Yulang.GeneralDeclarativeOrigins321 (Supported restriction)
open Yulang.GeneralDeclarativeNestedView332 (Sources)

theorem real_ready_capture_binder_lifts_back_before_normalization_without_changing_raw_row
    {p : Problem} (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {auth : Supported (ordinary p) done}
    (idx : Sources (restriction auth)) (addr : HeadAddress) (keep : List Nat)
    (job : Nat) (r : CheckedCaptureHead p tab)
    (pass : readCaptureFromReadyHead p tab idx addr keep job = some r)
    (noJ : covered r.original.orig.original = true) :
    ∃ originalPose,
      pullPos r.original.orig.original r.allocated.written = some originalPose ∧
      atSource r.original.orig.original originalPose = some (.var r.allocated.captured.binder) ∧
      r.allocated.after.equations[r.allocated.rawOrdinal]? =
        some ⟨r.allocated.target,r.allocated.captured.term⟩ := by
  obtain ⟨addrExists,_,raw,normalized⟩ :=
    ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate p tab idx addr keep job r pass
  obtain ⟨path,picked,binder⟩ := pull_joinfree_normalized_binder_to_exact_written_source
    r.original.orig.original r.allocated.written r.allocated.captured.binder noJ normalized
  exact ⟨path,picked,binder,raw⟩

end Yulang.C466LiteralCapturePullback
