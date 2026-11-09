import Yulang.CommonRoleSourceAssociatedAdapter
import Yulang.CommonRoleFeedbackConfluence

/-! Final-source support audit. A recomputed equation view, not a replacement
saturation algorithm. Fixed receivers and supplied annotations remain fragment
restrictions. No stability or convergence of revalidation is claimed. -/
namespace Yulang.CommonRoleFeedbackSupport
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request Computed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
namespace Adapter
open CommonRoleSourceAssociatedAdapter
variable (registry : Registry) (root : SourceRequest n)
  (annotations : Node registry root → List (Request n))

/-- Each emitted token identifies exactly one source node. -/
theorem emitted_owner (q : Node registry root)
    (i : Fin (entries registry root annotations).length) :
    i ∈ emit registry root annotations q ↔
      ((entries registry root annotations).get i).1 = q := by
  simp [emit]

/-- For the actual source adapter, token monotonicity is exactly persistence
of every annotated reachable node. It is not weaker source-insensitive stability. -/
theorem monotone_iff (decode : List (Fin (entries registry root annotations).length) → State n) :
    CommonRoleFeedbackConfluence.EmissionMonotone registry root decode
      (emit registry root annotations) ↔
    ∀ a b, a ⊆ b → ∀ q, annotations q ≠ [] →
      Reach registry root (decode a) q → Reach registry root (decode b) q := by
  constructor
  · intro mono a b included q nonempty reachable
    obtain ⟨r, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨i, emitted, _⟩ := emitted_complete registry root annotations q r member
    obtain ⟨other, reached, again⟩ := mono a b included i ⟨q, reachable, emitted⟩
    have equal : other = q := ((emitted_owner registry root annotations other i).mp again).symm.trans
      ((emitted_owner registry root annotations q i).mp emitted)
    simpa [equal] using reached
  · intro persists a b included i origin
    obtain ⟨q, reachable, emitted⟩ := origin
    have member := emitted_sound registry root annotations q i emitted
    have nonempty : annotations q ≠ [] := by intro h; simp [h] at member
    exact ⟨q, persists a b included q nonempty reachable, emitted⟩
end Adapter

variable (registry : Registry) (root : SourceRequest n)
  (annotations : Node registry root → List (Request n))

def supported (observation : State n) : List (Request n) :=
  (saturate registry root observation).flatMap annotations

/-- The executable support view contains exactly annotations on actual reachable
source nodes at the observation state, with no history/provenance assumption. -/
theorem supported_exact (observation : State n) (r : Request n) :
    r ∈ supported registry root annotations observation ↔
      ∃ q, Reach registry root observation q ∧ r ∈ annotations q := by
  simp only [supported, List.mem_flatMap, saturate_exact]

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

def revalidate (seed observation : State n) : State n :=
  CommonRoleAssociatedBatch.run env roles wf
    (supported registry root annotations observation) seed

/-- Soundness and completeness of revalidated equations for arbitrary registries,
roots, annotations, seed/observation states and assignments. This theorem does NOT
assert that Reach at the returned state equals Reach at observation. -/
theorem revalidate_exact (seed observation : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (revalidate registry root annotations env roles wf seed observation).atoms ↔
    All Common.model assignment seed.atoms ∧
      ∀ q, Reach registry root observation q → ∀ r ∈ annotations q, ∀ head,
        Computed env roles wf r head → Common.Equivalent (assignment r.output).1 (.base head) := by
  rw [revalidate, CommonRoleAssociatedBatch.run_models]
  constructor
  · rintro ⟨initial, obligations⟩
    exact ⟨initial, fun q reach r member head computed => obligations r
      ((supported_exact registry root annotations observation r).mpr ⟨q, reach, member⟩) head computed⟩
  · rintro ⟨initial, obligations⟩
    refine ⟨initial, ?_⟩
    intro r member head computed
    obtain ⟨q, reach, annotated⟩ := (supported_exact registry root annotations observation r).mp member
    exact obligations q reach r annotated head computed

/-- If every collected token still has a reachable emitting source, the original
persistent final state and the revalidated view have exactly the same models.
This is a per-run certificate, not an assumed universal monotonicity theorem. -/
theorem certified_final_models
    (seed : State n)
    (supportedHistory : ∀ i ∈ CommonRoleAssociatedFeedback.collected env roles wf registry root seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations)
        (CommonRoleSourceAssociatedAdapter.emit registry root annotations),
      ∃ q, Reach registry root
        (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations) q ∧
        i ∈ CommonRoleSourceAssociatedAdapter.emit registry root annotations q)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment
      (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations).atoms ↔
    All Common.model assignment
      (revalidate registry root annotations env roles wf seed
        (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations)).atoms := by
  rw [revalidate_exact]
  constructor
  · intro models
    refine ⟨?_, ?_⟩
    · exact ((CommonRoleAssociatedFeedback.final_models env roles wf registry root seed
        (CommonRoleSourceAssociatedAdapter.table registry root annotations)
        (CommonRoleSourceAssociatedAdapter.emit registry root annotations) assignment).mp models).1
    · intro q reach r member head computed
      exact CommonRoleSourceAssociatedAdapter.reachable_equation registry root env roles wf seed
        annotations assignment models q reach r member head computed
  · rintro ⟨initial, obligations⟩
    apply (CommonRoleAssociatedFeedback.final_models env roles wf registry root seed
      (CommonRoleSourceAssociatedAdapter.table registry root annotations)
      (CommonRoleSourceAssociatedAdapter.emit registry root annotations) assignment).mpr
    refine ⟨initial, ?_⟩
    intro i member head computed
    obtain ⟨q, reach, emitted⟩ := supportedHistory i member
    exact obligations q reach _
      (CommonRoleSourceAssociatedAdapter.emitted_sound registry root annotations q i emitted) head computed

def activeTokens (seed : State n) :=
  (saturate registry root
    (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations)).flatMap
    (CommonRoleSourceAssociatedAdapter.emit registry root annotations)

def unsupportedTokens (seed : State n) :=
  (CommonRoleAssociatedFeedback.collected env roles wf registry root seed
    (CommonRoleSourceAssociatedAdapter.table registry root annotations)
    (CommonRoleSourceAssociatedAdapter.emit registry root annotations)).filter
    (fun i => !(activeTokens registry root annotations env roles wf seed).contains i)

/-- An executable final-support check suffices for exact model agreement.
It is not a convergence theorem or a claim that the check always succeeds. -/
theorem checked_final_models (seed : State n)
    (check : unsupportedTokens registry root annotations env roles wf seed = [])
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment
      (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations).atoms ↔
    All Common.model assignment
      (revalidate registry root annotations env roles wf seed
        (CommonRoleSourceAssociatedAdapter.finalState registry root env roles wf seed annotations)).atoms := by
  apply certified_final_models registry root annotations env roles wf seed ?_ assignment
  intro i member
  have active : i ∈ activeTokens registry root annotations env roles wf seed := by
    apply Classical.byContradiction
    intro absent
    have bad : i ∈ unsupportedTokens registry root annotations env roles wf seed := by
      apply List.mem_filter.mpr
      exact ⟨member, by simp [absent]⟩
    rw [check] at bad
    cases bad
  obtain ⟨q, reachable, emitted⟩ := List.mem_flatMap.mp active
  exact ⟨q, (saturate_exact registry root _ q).mp reachable, emitted⟩
end Yulang.CommonRoleFeedbackSupport
