import Yulang.GeneralDeclarativeAlternativeSpine333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeSpineComplete333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Offer Index Covers exact_offer)
open GeneralDeclarativeAlternativeSpine333 (isPrefix peel_terminal peel_variable finishing through spines literals)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeNestedTail332 (peel isTerminal ClosedAt)
open GeneralDeclarativeNestedSeek332 (terminal_seen)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)

theorem terminal_in {s : State} {src : Index s} (link : Alias s root owner)
    (stored : (⟨owner,withTail row term⟩ : Equation) ∈ s.equations)
    (seen : (⟨owner,withTail row term,link,stored⟩ : Offer s root) ∈ src root)
    (ending : Terminal term) (fuel : Nat) :
    ∃ out ∈ spines src root (fuel+1), out.val = (row,term) := by
  let e : Offer s root := ⟨owner,withTail row term,link,stored⟩
  obtain ⟨t,eq⟩ := terminal_seen ending
  have p : peel e.rhs = (row,term) := peel_terminal ending row
  have finished : ∃ x, isTerminal (peel e.rhs).2 = some x := by rw [p]; exact ⟨t,eq⟩
  refine ⟨⟨(row,term),.inline link ending stored⟩,
    List.mem_flatMap.mpr ⟨e,seen,List.mem_append_left _ ?_⟩,rfl⟩
  unfold finishing
  dsimp only
  split
  · rename_i denied
    obtain ⟨_,ha⟩ := finished
    rw [ha] at denied
    cases denied
  · apply List.mem_singleton.mpr
    exact Subtype.ext p.symm

theorem prefix_in {s : State} {src : Index s} (link : Alias s root owner)
    (stored : (⟨owner,withTail front (.variable n)⟩ : Equation) ∈ s.equations)
    (seen : (⟨owner,withTail front (.variable n),link,stored⟩ : Offer s root) ∈ src root)
    {info : ClosedAt s n} (known : info ∈ spines src n fuel) :
    ∃ out ∈ spines src root (fuel+1), out.val = (front++info.val.1,info.val.2) := by
  let e : Offer s root := ⟨owner,withTail front (.variable n),link,stored⟩
  have p : peel e.rhs = (front,.variable n) := peel_variable front n
  have shape : isPrefix (peel e.rhs).2 = some n := by rw [p]; rfl
  refine ⟨⟨_,.prefixed link stored info.property⟩,
    List.mem_flatMap.mpr ⟨e,seen,List.mem_append_right _ ?_⟩,rfl⟩
  unfold through
  dsimp only
  split
  · rename_i denied
    rw [shape] at denied
    cases denied
  · rename_i j printed
    have same := Option.some.inj (printed.symm.trans shape)
    subst j
    exact List.mem_map.mpr ⟨info,known,Subtype.ext (congrArg (fun z => (z.1 ++ info.val.1,info.val.2)) p)⟩

/-- Every independently derived spine is found once its authorized
rows/aliases are included and the syntax depth is large enough. -/
theorem spine_complete {s : State} {src : Index s} (covers : Covers src) (pre : Spine s n row term) :
    ∃ bound, ∀ fuel ≥ bound, ∃ out ∈ spines src n fuel, out.val = (row,term) := by
  induction pre with
  | width route known =>
    exact ⟨1,fun fuel enough => by
      cases fuel with
      | zero => cases enough
      | succ fuel => exact terminal_in (row := []) route known (exact_offer (covers _ _ _ route known) route known) .width fuel⟩
  | exactEnd route known =>
    exact ⟨1,fun fuel enough => by
      cases fuel with
      | zero => cases enough
      | succ fuel => exact terminal_in (row := []) route known (exact_offer (covers _ _ _ route known) route known) .exactEnd fuel⟩
  | inline route terminal known =>
    exact ⟨1,fun fuel enough => by
      cases fuel with
      | zero => cases enough
      | succ fuel => exact terminal_in route known (exact_offer (covers _ _ _ route known) route known) terminal fuel⟩
  | cons route known _ ih =>
    obtain ⟨bound,here⟩ := ih
    refine ⟨bound+1,fun fuel enough => ?_⟩
    cases fuel with
    | zero => cases enough
    | succ fuel =>
      obtain ⟨a,got,h⟩ := here fuel (Nat.le_of_succ_le_succ enough)
      obtain ⟨result,listed,same⟩ := prefix_in (front := [(_,Expr.variable _)]) route known
        (exact_offer (covers _ _ _ route known) route known) got
      exact ⟨result,listed,by rw [same,h]; rfl⟩
  | prefixed route known _ ih =>
    obtain ⟨bound,here⟩ := ih
    refine ⟨bound+1,fun fuel enough => ?_⟩
    cases fuel with
    | zero => cases enough
    | succ fuel =>
      obtain ⟨a,got,h⟩ := here fuel (Nat.le_of_succ_le_succ enough)
      obtain ⟨result,listed,same⟩ := prefix_in route known
        (exact_offer (covers _ _ _ route known) route known) got
      exact ⟨result,listed,by rw [same,h]⟩

theorem literal_complete {s : State} {src : Index s} (covers : Covers src) (known : Closed s raw row term) :
    ∃ bound, ∀ fuel ≥ bound, ∃ out ∈ literals src fuel raw, out.val = (row,term) := by
  induction known with
  | terminal ending =>
    cases ending
    · exact ⟨0,fun _ _ => ⟨_,List.mem_cons_self,rfl⟩⟩
    · exact ⟨0,fun _ _ => ⟨_,List.mem_cons_self,rfl⟩⟩
  | field _ ih =>
    obtain ⟨bound,after⟩ := ih
    refine ⟨bound,fun fuel enough => ?_⟩
    obtain ⟨x,got,same⟩ := after fuel enough
    exact ⟨_,List.mem_map.mpr ⟨x,got,rfl⟩,congrArg (fun v => (_ :: v.1,v.2)) same⟩
  | name found =>
    obtain ⟨bound,after⟩ := spine_complete covers found
    refine ⟨bound,fun fuel enough => ?_⟩
    obtain ⟨x,got,same⟩ := after fuel enough
    exact ⟨_,List.mem_map.mpr ⟨x,got,rfl⟩,same⟩

end Yulang.GeneralDeclarativeAlternativeSpineComplete333
