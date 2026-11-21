import Yulang.GeneralFiniteRawPresentation306
import Yulang.GeneralDeferredLadderControlCover304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLadderCompiledPresentation306
open GeneralDeferredLadderControl304 (Control view successors successors_exact Edge remaining edge_consumes_one)
open GeneralDeferredLadderControlCover304 (allStates all_exact every_control_realized)
open GeneralDeferredLadderControlBridge304 (executable_exact)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderRefresh301 (before)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)
open GeneralFiniteRawPresentation306 (Presentation)
open GeneralFiniteColoredRounds306 (Closed On)

def Reach (n : Nat) (s : State roles) : Prop := ∃ length, Counted length (before n) s

theorem closure (n : Nat) : Closed (successors n) (allStates n) := by
  intro x _ y edge
  have parsed := (successors_exact n x y).mp edge
  cases parsed with
  | install _ bound => exact (all_exact ..).mpr (by simpa using Nat.succ_le_succ bound)
  | observe bound => exact (all_exact ..).mpr bound

theorem present (n : Nat) :
    Presentation (Reach n) RawStep (view n) (fun _ => ()) (successors n) (fun _ => ()) (allStates n) := by
  refine ⟨closure n,?_,?_,fun _ _ => rfl,?_⟩
  · rintro s ⟨i,path⟩
    exact (every_control_realized n _).mpr ⟨i,s,path,rfl⟩
  · rintro s t ⟨i,path⟩ edge
    exact ⟨i+1,.tail path edge⟩
  · rintro s ⟨i,path⟩ goal
    exact executable_exact n path goal

theorem level_bound (n : Nat) {x : Control} (here : x ∈ allStates n) :
    remaining n x ≤ n+2 := by
  have cap := (all_exact n x).mp here
  cases x with
  | mk i tag =>
    cases tag <;> simp [remaining] <;> omega

theorem all_levels (n k : Nat) (bound : k ≤ n+2) :
    ∃ c ∈ allStates n, remaining n c = k := by
  by_cases high : k = n+2
  · exact ⟨⟨0,false⟩,(all_exact ..).mpr (Nat.zero_le _),by simp [remaining,high]⟩
  · let c : Control := ⟨n+1-k,true⟩
    refine ⟨c,(all_exact ..).mpr (Nat.sub_le ..),?_⟩
    simp only [remaining,c,ite_true,Nat.add_zero]
    omega

theorem possible (n : Nat) (x : Control) (here : x ∈ allStates n) :
    (∃ y ∈ successors n x, True) ↔ 0 < remaining n x := by
  constructor
  · rintro ⟨y,step,_⟩
    have drops := edge_consumes_one ((successors_exact ..).mp step)
    omega
  · intro left
    obtain ⟨i,seen⟩ := x
    by_cases fits : i ≤ n
    · exact ⟨⟨i+1,seen⟩,(successors_exact ..).mpr (.install seen fits),trivial⟩
    · have cap := (all_exact ..).mp here
      change i ≤ n+1 at cap
      have last : i = n+1 := by omega
      subst i
      cases seen
      · exact ⟨⟨n+1,true⟩,(successors_exact ..).mpr (.observe (Nat.le_refl _)),trivial⟩
      · simp [remaining] at left

theorem level_bisim (n : Nat) :
    On (successors n) (fun _ => ()) (allStates n) (fun x y => remaining n x = remaining n y) := by
  intro x xm y ym same
  refine ⟨rfl,?_,?_⟩
  · intro a step
    have first := edge_consumes_one ((successors_exact ..).mp step)
    obtain ⟨b,taken,_⟩ := (possible n y ym).mpr (by omega)
    have last := edge_consumes_one ((successors_exact ..).mp taken)
    exact ⟨b,taken,by omega⟩
  · intro b step
    have first := edge_consumes_one ((successors_exact ..).mp step)
    obtain ⟨a,taken,_⟩ := (possible n x xm).mpr (by omega)
    have last := edge_consumes_one ((successors_exact ..).mp taken)
    exact ⟨a,taken,by omega⟩

theorem any_bisim_level (n : Nat) {rel : Control → Control → Prop}
    (checked : On (successors n) (fun _ => ()) (allStates n) rel)
    (x y : Control) (xm : x ∈ allStates n) (ym : y ∈ allStates n) (same : rel x y) :
    remaining n x = remaining n y := by
  by_cases left : 0 < remaining n x
  · obtain ⟨a,step,_⟩ := (possible n x xm).mpr left
    obtain ⟨b,taken,linked⟩ := (checked x xm y ym same).2.1 a step
    have smaller := any_bisim_level n checked a b (closure n x xm a step) (closure n y ym b taken) linked
    have first := edge_consumes_one ((successors_exact ..).mp step)
    have last := edge_consumes_one ((successors_exact ..).mp taken)
    omega
  · by_cases right : 0 < remaining n y
    · obtain ⟨b,taken,_⟩ := (possible n y ym).mpr right
      obtain ⟨a,step,_⟩ := (checked x xm y ym same).2.2 b taken
      have first := edge_consumes_one ((successors_exact ..).mp step)
      omega
    · omega
termination_by remaining n x + remaining n y
decreasing_by
  have first := edge_consumes_one ((successors_exact ..).mp step)
  have last := edge_consumes_one ((successors_exact ..).mp taken)
  omega

end Yulang.GeneralLadderCompiledPresentation306
