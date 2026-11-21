import Yulang.GeneralDeclarativeAggregate324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregatePoint324
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeAggregate324 (span aggregates ready ready_iff assembled)
open GeneralDeclarativeMerge320 (Merge shared_center lower upper lower_exact upper_exact equality_sound)
open GeneralDeclarativeEntailment320 (Entails appendFacts conservative_append)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent model subtype_refl subtype_trans)
open Core.PresenceGeneration (TyTerm)

def Points (seed : Capture) (rest : List Capture) : Prop :=
  ∀ occurrence ∈ seed :: rest,
    occurrence.lower = occurrence.center ∧ occurrence.upper = occurrence.center

theorem point_aggregate {s : State} {seed : Capture} {rest : List Capture} {combined : Capture}
    (merged : Merge s seed rest combined) (points : Points seed rest)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m combined.lower).1 (m combined.center).1 ∧
    Equivalent (m combined.upper).1 (m combined.center).1 := by
  have center := shared_center merged m valid
  have eqLo := equality_sound merged.lowerEq m valid
  have eqHi := equality_sound merged.upperEq m valid
  have low : Equivalent ((lower seed rest).eval model m) (m combined.center).1 := by
    constructor
    · apply (lower_exact m seed rest _).mpr
      intro entry used
      rw [(points entry used).1]
      exact (center.2 entry used).1
    · have first := (lower_exact m seed rest _).mp (subtype_refl ((lower seed rest).eval model m)) seed List.mem_cons_self
      rw [(points seed List.mem_cons_self).1] at first
      exact subtype_trans (center.2 seed List.mem_cons_self).2 first
  have high : Equivalent ((upper seed rest).eval model m) (m combined.center).1 := by
    constructor
    · have first := (upper_exact m seed rest _).mp (subtype_refl ((upper seed rest).eval model m)) seed List.mem_cons_self
      rw [(points seed List.mem_cons_self).2] at first
      exact subtype_trans first (center.2 seed List.mem_cons_self).1
    · apply (upper_exact m seed rest _).mpr
      intro entry used
      rw [(points entry used).2]
      exact (center.2 entry used).2
  exact ⟨eqv_trans eqLo low,eqv_trans eqHi high⟩

def aliases (combined : Capture) : List Equation :=
  [⟨combined.lower,.variable combined.center⟩,⟨combined.upper,.variable combined.center⟩]

def observable (s : State) (protect : List Nat) (seed : Capture) (rest : List Capture) : State :=
  appendFacts (ready s protect seed rest) (aliases (span s protect seed rest))

/-- Point aggregate equations can therefore be added to the ordinary
normalized input view without narrowing any model; they are not guessed
independently of the input proofs. General nonpoint aggregates are not
replaced by their center. -/
theorem aliases_proved {s : State} {seed : Capture} {rest : List Capture}
    (known : ∀ occurrence ∈ seed :: rest, Bounds s occurrence) (points : Points seed rest) :
    ∀ row ∈ aliases (span s protect seed rest), Entails (ready s protect seed rest) row := by
  intro row there m valid
  have center := point_aggregate (assembled (extra := protect) known) points m
    ((ready_iff (extra := protect) known m).mp valid)
  rcases List.mem_cons.mp there with rfl|later
  · exact center.1
  · cases List.mem_singleton.mp later
    exact center.2

theorem observable_models {s : State} {seed : Capture}
    (known : ∀ occurrence ∈ seed :: rest, Bounds s occurrence) (points : Points seed rest)
    (m : Assignment) :
    Models (observable s protect seed rest) m ↔ Models (ready s protect seed rest) m :=
  conservative_append (aliases_proved (protect := protect) known points) m

end Yulang.GeneralDeclarativeAggregatePoint324
