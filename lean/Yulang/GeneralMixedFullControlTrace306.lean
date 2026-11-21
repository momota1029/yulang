import Yulang.GeneralMixedFullControlStep306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlTrace306
open GeneralMixedFullControlCode306 (Code Event code fire Action action_step)
open GeneralDictionaryOutputDepth252 (roles initial root registry)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralMixedFullControlStep306 (split forward lifts)

inductive RawRoute : State roles → List (Event × Code) → State roles → Prop
  | done (s : State roles) : RawRoute s [] s
  | append : Action e s t → RawRoute t rest u → RawRoute s ((e,code t)::rest) u

def check (x : Code) (goal : Code) : List (Event × Code) → Bool
  | [] => decide (x = goal)
  | (event,mid)::rest => fire event x mid && check mid goal rest

theorem encode {s t : State roles} {n : Nat} (before : ActualPath initial s n) (route : RawRoute s trace t) :
    check (code s) (code t) trace = true := by
  induction route generalizing n with
  | done => simp [check]
  | append step _ ih =>
    exact Bool.and_eq_true_iff.mpr ⟨forward before step,ih (.more before (action_step step))⟩

theorem decode {s : State roles} {n : Nat} (path : ActualPath initial s n)
    (accepted : check (code s) goal trace = true) :
    ∃ t, RawRoute s trace t ∧ code t = goal := by
  induction trace generalizing s n with
  | nil => exact ⟨s,.done s,of_decide_eq_true accepted⟩
  | cons entry rest ih =>
    obtain ⟨e,desired⟩ := entry
    obtain ⟨edge,remainder⟩ := Bool.and_eq_true_iff.mp accepted
    obtain ⟨next,actual,found⟩ := lifts path e desired edge
    have a : check (code next) goal rest = true := found.symm ▸ remainder
    obtain ⟨last,run,eq⟩ := ih (.more path (action_step actual)) a
    exact ⟨last,found ▸ (RawRoute.append actual run),eq⟩

theorem exact_checker {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    check (code s) goal trace = true ↔ ∃ t, RawRoute s trace t ∧ code t = goal :=
  ⟨decode path,fun ⟨_,run,eq⟩ => eq ▸ encode path run⟩

theorem concat {s t : State roles} {n : Nat} (path : ActualPath initial s n) (route : RawRoute s trace t) :
    ActualPath initial t (n + trace.length) := by
  induction route generalizing n with
  | done => simpa
  | append step _ ih =>
    have progress := ih (.more path (action_step step))
    simpa only [List.length_cons,Nat.add_right_comm n 1,Nat.add_assoc] using progress

theorem initial_code : code initial = ⟨false,⟨false,false⟩⟩ := by decide +kernel

theorem all_constructible (x : Code) : ∃ s n, ActualPath initial s n ∧ code s = x := by
  let scalar : Event := .scalar (if x.scalars.zero then 0 else 1)
  let mid : Code := ⟨false,x.scalars⟩
  let xs := (if x.scalars = ⟨false,false⟩ then [] else [(scalar,mid)]) ++
    (if x.installed then [(.install,x)] else [])
  have yes : check (code initial) x xs = true := by
    rw [initial_code]
    rcases x with ⟨a,⟨b,c⟩⟩
    cases a <;> cases b <;> cases c <;> decide
  obtain ⟨s,route,eq⟩ := decode (.empty _) yes
  exact ⟨s,0+xs.length,concat (.empty _) route,eq⟩

end Yulang.GeneralMixedFullControlTrace306
