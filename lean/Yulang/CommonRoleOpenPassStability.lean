import Yulang.CommonRoleOpenRecursivePass
import Yulang.CommonRoleOpenFiniteClosure

/-! Semantic idempotence of the existing fixed structural recursive pass.
This does not assert syntactic state/trace stabilization or saturation of a
state-dependent source frontier. -/
namespace Yulang.CommonRoleOpenPassStability
open CommonRoleSettledConstraints (State)
open CommonRoleOpenProducer (Request Registry)
open CommonRoleOpenPropagation (Allocation prepare produce update childList)
open CommonRoleOpenRecursivePass (run)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleCandidateConstraints (Compatible)
open CommonRoleOpenFiniteClosure (Reach next)

/-- Every statically reachable structural request contributes its capture obligations. -/
def Good (registry : Registry) (allocate : Allocation n) (q : Request)
    (assignment : Fin n → Comp Common.model) : Prop :=
  ∀ target, Reach registry q target →
    Compatible (update registry.declarations allocate target) assignment

theorem good_unfold (registry : Registry) (allocate : Allocation n) (q : Request)
    (assignment : Fin n → Comp Common.model) :
    Good registry allocate q assignment ↔
      Compatible (update registry.declarations allocate q) assignment ∧
      ∀ child ∈ next registry q, Good registry allocate child assignment := by
  constructor
  · intro h
    refine ⟨h q .refl, ?_⟩
    intro child member target reached
    exact h target (.step ((CommonRoleOpenFiniteClosure.mem_next ..).mp member) reached)
  · rintro ⟨here, below⟩ target reached
    cases reached with
    | refl => exact here
    | step edge rest => exact below _ ((CommonRoleOpenFiniteClosure.mem_next ..).mpr edge) _ rest

theorem produce_of_model (registry : Registry) (allocate : Allocation n)
    (q : Request) (s : State n) (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (prepare registry.declarations allocate q s).atoms) :
    childList (produce registry.declarations allocate q s) = next registry q := by
  have yes := (CommonRoleOpenPropagation.consistent_exact _).mpr ⟨assignment, model⟩
  simp only [produce, yes, ↓reduceIte]
  unfold childList next
  cases CommonRoleOpenProducer.frontier registry.declarations q <;> rfl

theorem thread_models (worker : Request → State n → β × State n)
    (property : Request → Prop) (xs : List Request)
    (assignment : Fin n → Comp Common.model)
    (exactness : ∀ child ∈ xs, ∀ before,
      All Common.model assignment (worker child before).2.atoms ↔
        All Common.model assignment before.atoms ∧ property child)
    (s : State n) :
    All Common.model assignment (CommonRoleOpenThreading.thread worker xs s).2.atoms ↔
      All Common.model assignment s.atoms ∧ ∀ child ∈ xs, property child := by
  induction xs generalizing s with
  | nil => simp [CommonRoleOpenThreading.thread]
  | cons child rest ih =>
    simp only [CommonRoleOpenThreading.thread]
    rw [ih (fun c mem => exactness c (List.mem_cons_of_mem _ mem))]
    rw [exactness child List.mem_cons_self]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

theorem run_state (registry : Registry) (allocate : Allocation n) (q : Request)
    (s : State n) :
    (run registry allocate q s).2 =
      (CommonRoleOpenThreading.thread (run registry allocate)
        (childList (produce registry.declarations allocate q s))
        (prepare registry.declarations allocate q s)).2 := by
  rw [CommonRoleOpenRecursivePass.run_unfold]

set_option maxHeartbeats 2000000 in
theorem run_models_exact (registry : Registry) (allocate : Allocation n) (q : Request)
    (s : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (run registry allocate q s).2.atoms ↔
      All Common.model assignment s.atoms ∧ Good registry allocate q assignment := by
  have accessible := CommonRoleOpenProducerAccess.accessible registry q
  induction accessible generalizing s with
  | intro q predecessors ih =>
    let prepared := prepare registry.declarations allocate q s
    let cs := childList (produce registry.declarations allocate q s)
    have threads : All Common.model assignment
        (CommonRoleOpenThreading.thread (run registry allocate) cs prepared).2.atoms ↔
        All Common.model assignment prepared.atoms ∧
          ∀ child ∈ cs, Good registry allocate child assignment := by
      apply thread_models
      intro child member before
      exact ih child (CommonRoleOpenRecursivePass.child_origin
        registry.declarations allocate q s child member) before
    rw [run_state]
    change All Common.model assignment
      (CommonRoleOpenThreading.thread (run registry allocate) cs prepared).2.atoms ↔ _
    rw [threads]
    constructor
    · rintro ⟨models, children⟩
      have same : cs = next registry q := produce_of_model registry allocate q s assignment models
      obtain ⟨original, here⟩ := (CommonRoleOpenPropagation.prepare_exact ..).mp models
      exact ⟨original, (good_unfold registry allocate q assignment).mpr
        ⟨here, by simpa only [same] using children⟩⟩
    · rintro ⟨original, good⟩
      obtain ⟨here, children⟩ := (good_unfold registry allocate q assignment).mp good
      have models : All Common.model assignment prepared.atoms :=
        (CommonRoleOpenPropagation.prepare_exact ..).mpr ⟨original, here⟩
      have same : cs = next registry q := produce_of_model registry allocate q s assignment models
      exact ⟨models, by simpa only [same] using children⟩

/-- Running this fixed structural pass a second time does not change its models.
The atom list may still grow, so this is semantic rather than syntactic stability. -/
theorem run_semantically_idempotent (registry : Registry) (allocate : Allocation n)
    (q : Request) (s : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment
      (run registry allocate q (run registry allocate q s).2).2.atoms ↔
      All Common.model assignment (run registry allocate q s).2.atoms := by
  rw [run_models_exact, run_models_exact]
  exact ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

end Yulang.CommonRoleOpenPassStability
