import Yulang.GeneralDeclarativeWitnessCycle350
import Yulang.GeneralDeclarativeUnfinishedRoot330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrigins350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Origin Supported restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (constructorTag)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

/-- Independent provenance projection, not solver witness data. Release
identifiers are anchored by the caller exactly like authored clauses. -/
structure Table where
  authored : List Equation
  produced : List (Equation × Nat)
  released : List Nat

structure Attached (s : State) (t : Table) : Type where
  authored : t.authored ⊆ s.equations
  produced : ∀ p ∈ t.produced, p.1 ∈ s.equations

def attach (s : State) (t : Table) : Option (Attached s t) :=
  if a : t.authored.all (fun e => decide (e ∈ s.equations)) = true then
    if b : t.produced.all (fun q => decide (q.1 ∈ s.equations)) = true then
      some ⟨fun e h => of_decide_eq_true (List.all_eq_true.mp a e h),
        fun e h => of_decide_eq_true (List.all_eq_true.mp b e h)⟩
    else none
  else none

def origin (t : Table) (e : Equation) : Origin → Prop
  | .source => e ∈ t.authored
  | .output owner => (e,owner) ∈ t.produced

def support {s : State} {t : Table} (a : Attached s t) : Supported s (· ∈ t.released) :=
  ⟨origin t,fun {e o} proof => match o with
   | .source => a.authored proof
   | .output n => a.produced (e,n) proof⟩

def visible (t : Table) : List Equation :=
  t.authored ++ (t.produced.filter fun q => t.released.contains q.2).map Prod.fst

/-- Every exactly recorded provenance route is included; an ordinary
equation alone is not an origin and a pending owner is not released. -/
theorem visible_iff {s : State} {t : Table} (a : Attached s t) (e : Equation) :
    e ∈ (restriction (support a)).equations ↔ e ∈ visible t := by
  rw [backed_iff]
  constructor
  · rintro ⟨o,why,good⟩
    cases good with
    | source => exact List.mem_append_left _ why
    | @completed owner confirmed =>
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨(e,owner),List.mem_filter.mpr ⟨why,by simpa using confirmed⟩,rfl⟩)
  · intro authorized
    rcases List.mem_append.mp authorized with yes|later
    · exact ⟨.source,yes,.source⟩
    · obtain ⟨⟨_,owner⟩,whereFrom,equal⟩ := List.mem_map.mp later
      cases equal
      obtain ⟨produced,done⟩ := List.mem_filter.mp whereFrom
      exact ⟨.output owner,produced,.completed (by simpa using done)⟩

end Yulang.GeneralDeclarativeWitnessOrigins350
