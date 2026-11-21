import Yulang.GeneralDeclarativeTermOccurrences322
import Yulang.GeneralDeclarativeNameLookup322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTermCapture322
open GeneralDeclarativeTermWalk322 (Occurrence Walk Binds)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeNameLookup322 (find exact_found found_if)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalMaterialization (Mode)

def first (seen : List Occurrence) (binder : Nat) : Option Occurrence :=
  seen.find? (fun o => decide (o.binder = binder ∧ o.mode = .actual))

theorem repr_found {seen : List Occurrence} {n : Nat} {row : Occurrence}
    (found : first seen n = some row) :
    row ∈ seen ∧ row.binder = n ∧ row.mode = .actual := by
  unfold first at found
  exact ⟨List.mem_of_find?_eq_some found,of_decide_eq_true
    (List.find?_some (p := fun o : Occurrence => decide (o.binder = n ∧ o.mode = .actual)) found)⟩

theorem occurs_if {seen : List Occurrence} {row : Occurrence}
    (there : row ∈ seen) (actual : row.mode = .actual) :
    ∃ rep, first seen row.binder = some rep := by
  cases clicked : first seen row.binder with
  | some rep => exact ⟨rep,rfl⟩
  | none =>
    unfold first at clicked
    have denied := List.find?_eq_none.mp clicked row there
    simp [actual] at denied

noncomputable def named (s : State) (seen : List Occurrence) (pool : Nat → List Nat)
    (initial : Nat → Capture) (n : Nat) : Capture :=
  ⟨(initial n).lower, ((first seen n).bind fun o => find s (pool n) o.term).getD (initial n).center,
    (initial n).upper⟩

def Shared (s : State) (seen : List Occurrence) : Prop :=
  ∀ a ∈ seen, ∀ b ∈ seen, a.binder = b.binder → a.mode = .actual → b.mode = .actual →
    Derives s a.term b.term

def KnownNames (s : State) (seen : List Occurrence) (pool : Nat → List Nat) : Prop :=
  ∀ chosen ∈ seen, chosen.mode = .actual → ∃ n ∈ pool chosen.binder,
    Derives s (.variable n) chosen.term

/-- All real occurrences of one binder use one common ordinary name
chosen from the first occurrence. Lower and upper bounds are not replaced
by that first occurrence and can carry a verified aggregate interval. -/
theorem named_binds {s : State} {all seen : List Occurrence}
    (includeSeen : seen ⊆ all) (ties : Shared s all) (found : KnownNames s all pool)
    (read : Walk .actual term code seen) :
    Binds s (named s all pool initial) seen := by
  intro leaf inside
  have md := (actual_positions read).2 leaf inside
  obtain ⟨rep,hit⟩ := occurs_if (includeSeen inside) md
  obtain ⟨here,binder,sameMode⟩ := repr_found hit
  obtain ⟨n,hn⟩ := found_if (found rep here sameMode)
  have keep : find s (pool leaf.binder) rep.term = some n := binder ▸ hn
  have depth := ties leaf (includeSeen inside) rep here binder.symm md sameMode
  have recipe : Derives s leaf.term (.variable n) :=
    .trans depth (.symm (exact_found hn).2)
  simpa only [md,byMode,named,hit,Option.bind_some,keep,Option.getD_some] using recipe

end Yulang.GeneralDeclarativeTermCapture322
