import Yulang.CommonRoleRefreshDriver

/-! Autonomous finite feedback, relative to an explicit finite update adapter.
`decode` and `emit` are supplied, not yet derived from associated declarations.
This is an implementation restriction, not a language rejection rule. No least
solution, order independence, or full B4 typing exactness is claimed. -/
namespace Yulang.CommonRoleFiniteFeedback
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)

/-- Generic finite feedback may recompute its rules non-monotonically. -/
def loop (rules : List (Fin k) → List (FiniteHorn.Rule (Fin k))) :
    Nat → List (Fin k) → List (Fin k)
  | 0, seen => seen
  | fuel + 1, seen =>
    match FiniteHorn.firstFresh (rules seen) seen (List.finRange k) with
    | none => seen
    | some fact => loop rules fuel (fact :: seen)

theorem loop_nodup (rules : List (Fin k) → List (FiniteHorn.Rule (Fin k)))
    (fuel : Nat) (seen : List (Fin k)) (distinct : seen.Nodup) :
    (loop rules fuel seen).Nodup := by
  induction fuel generalizing seen with
  | zero => exact distinct
  | succ fuel ih =>
    simp only [loop]
    cases found : FiniteHorn.firstFresh (rules seen) seen (List.finRange k) with
    | none => exact distinct
    | some fact => exact ih _ (List.nodup_cons.mpr
        ⟨(FiniteHorn.firstFresh_some _ _ _ found).2.1, distinct⟩)

/-- The cardinal bound is enough even if newly generated edges disappear. -/
theorem loop_closed (rules : List (Fin k) → List (FiniteHorn.Rule (Fin k)))
    (fuel : Nat) (seen : List (Fin k)) (distinct : seen.Nodup)
    (enough : k ≤ seen.length + fuel) :
    ∀ fact, FiniteHorn.Enabled (rules (loop rules fuel seen))
      (loop rules fuel seen) fact → fact ∈ loop rules fuel seen := by
  induction fuel generalizing seen with
  | zero =>
    intro fact _
    exact FiniteWorklist.saturated (List.finRange k) seen (fun i => List.mem_finRange i)
      distinct (by simpa using enough) fact
  | succ fuel ih =>
    simp only [loop]
    cases found : FiniteHorn.firstFresh (rules seen) seen (List.finRange k) with
    | none =>
      intro fact enabled
      exact (FiniteHorn.firstFresh_none_iff _ _ _).mp found fact (List.mem_finRange fact) enabled
    | some fact =>
      apply ih _ (List.nodup_cons.mpr
        ⟨(FiniteHorn.firstFresh_some _ _ _ found).2.1, distinct⟩)
      simp only [List.length_cons]
      omega

/-- Each freshly enabled token comes from recomputed actual-producer reachability. -/
def feedbackRules (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))
    (seen : List (Fin k)) : List (FiniteHorn.Rule (Fin k)) :=
  ((saturate registry root (decode seen)).flatMap emit).map (fun f => ⟨[], f⟩)

theorem feedback_enabled (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))
    (seen : List (Fin k)) (fact : Fin k) :
    FiniteHorn.Enabled (feedbackRules registry root decode emit seen) seen fact ↔
      ∃ q, Reach registry root (decode seen) q ∧ fact ∈ emit q := by
  simp only [FiniteHorn.Enabled, feedbackRules, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨rule, ⟨f, ⟨q, present, emitted⟩, rfl⟩, rfl, _⟩
    exact ⟨q, (saturate_exact ..).mp present, emitted⟩
  · rintro ⟨q, reachable, emitted⟩
    exact ⟨⟨[], fact⟩, ⟨fact, ⟨q, (saturate_exact ..).mpr reachable, emitted⟩, rfl⟩,
      rfl, by simp⟩

def collect (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k)) : List (Fin k) :=
  loop (feedbackRules registry root decode emit) k []

theorem collect_nodup (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k)) :
    (collect registry root decode emit).Nodup := loop_nodup _ _ _ (by simp)

theorem collect_capacity (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k)) :
    (collect registry root decode emit).length ≤ k := by
  simpa using (collect_nodup registry root decode emit).length_le_of_subset
    (l₂ := List.finRange k) (fun i _ => List.mem_finRange i)

/-- Every final reachable parent's emitted update is already incorporated.
No external trace or closure assumption is required, but decode/emit remain inputs. -/
theorem collect_closed (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))
    (q : Node registry root)
    (reachable : Reach registry root (decode (collect registry root decode emit)) q)
    (fact : Fin k) (emitted : fact ∈ emit q) : fact ∈ collect registry root decode emit := by
  apply loop_closed (feedbackRules registry root decode emit) k [] (by simp) (by simp) fact
  exact (feedback_enabled ..).mpr ⟨q, reachable, emitted⟩

def visits (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k)) :=
  saturate registry root (decode (collect registry root decode emit))

theorem visits_exact (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))
    (q : Node registry root) : q ∈ visits registry root decode emit ↔
      Reach registry root (decode (collect registry root decode emit)) q := saturate_exact ..

end Yulang.CommonRoleFiniteFeedback
