import Yulang.GeneralDeclarativeAlternativeSpine333
import Yulang.GeneralDeclarativeAlternativeNeeds333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeSpineComplete333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeNeeds333 (Need Planned Eventually eventually_one eventually_step)
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

abbrev SpinesAt (src : Index s) (n : Nat) (row : Row Expr) (term : Expr) :=
  Eventually (fun fuel => ∃ out ∈ spines src n fuel, out.val = (row,term))

abbrev LiteralIn (src : Index s) (raw : Expr) (row : Row Expr) (term : Expr) :=
  Eventually (fun fuel => ∃ out ∈ literals src fuel raw, out.val = (row,term))

/-- A finite dependency packet is obtained from the actual independent
spine derivation. No globally complete alias index is required. -/
theorem spine_plan {s : State} (pre : Spine s n row term) :
    Planned (fun src : Index s => SpinesAt src n row term) := by
  induction pre with
  | @width root owner route known =>
    let e : Need s := ⟨root,⟨owner,_,route,known⟩⟩
    refine ⟨[e],fun src filled => eventually_one fun fuel => ?_⟩
    exact terminal_in (row := []) route known (filled e List.mem_cons_self) .width fuel
  | @exactEnd root owner route known =>
    let e : Need s := ⟨root,⟨owner,_,route,known⟩⟩
    refine ⟨[e],fun src filled => eventually_one fun fuel => ?_⟩
    exact terminal_in (row := []) route known (filled e List.mem_cons_self) .exactEnd fuel
  | @inline root owner term front route terminal known =>
    let e : Need s := ⟨root,⟨owner,_,route,known⟩⟩
    refine ⟨[e],fun src filled => eventually_one fun fuel => ?_⟩
    exact terminal_in route known (filled e List.mem_cons_self) terminal fuel
  | @cons root owner key field rest row term route known _ ih =>
    let e : Need s := ⟨root,⟨owner,_,route,known⟩⟩
    refine ih.add e (fun src to hand => eventually_step hand (fun fuel hit => ?_))
    obtain ⟨info,present,value⟩ := hit
    obtain ⟨out,found,shows⟩ := prefix_in (front := [(key,Expr.variable field)]) route known to present
    exact ⟨out,found,by rw [shows,value]; rfl⟩
  | @prefixed root owner front rest row term route known _ ih =>
    let e : Need s := ⟨root,⟨owner,_,route,known⟩⟩
    refine ih.add e (fun src to hand => eventually_step hand (fun fuel hit => ?_))
    obtain ⟨info,present,value⟩ := hit
    obtain ⟨out,found,shows⟩ := prefix_in route known to present
    exact ⟨out,found,by rw [shows,value]⟩

theorem spine_complete {s : State} {src : Index s} (covers : Covers src) (pre : Spine s n row term) :
    SpinesAt src n row term := (spine_plan pre).from_cover covers

theorem literal_plan {s : State} (known : Closed s raw row term) :
    Planned (fun src : Index s => LiteralIn src raw row term) := by
  induction known with
  | terminal ending =>
    cases ending
    · exact Planned.pure fun _ => ⟨0,fun _ _ => ⟨_,List.mem_cons_self,rfl⟩⟩
    · exact Planned.pure fun _ => ⟨0,fun _ _ => ⟨_,List.mem_cons_self,rfl⟩⟩
  | field _ ih =>
    apply ih.map
    intro src earlier
    obtain ⟨bound,after⟩ := earlier
    refine ⟨bound,fun fuel enough => ?_⟩
    obtain ⟨x,got,same⟩ := after fuel enough
    exact ⟨_,List.mem_map.mpr ⟨x,got,rfl⟩,congrArg (fun v => (_ :: v.1,v.2)) same⟩
  | name found =>
    apply (spine_plan found).map
    intro src earlier
    obtain ⟨bound,after⟩ := earlier
    refine ⟨bound,fun fuel enough => ?_⟩
    obtain ⟨x,got,same⟩ := after fuel enough
    exact ⟨_,List.mem_map.mpr ⟨x,got,rfl⟩,same⟩

theorem literal_complete {s : State} {src : Index s} (covers : Covers src) (known : Closed s raw row term) :
    LiteralIn src raw row term := (literal_plan known).from_cover covers

end Yulang.GeneralDeclarativeAlternativeSpineComplete333
