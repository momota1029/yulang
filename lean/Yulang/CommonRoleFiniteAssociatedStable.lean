import Yulang.CommonRoleFiniteAssociatedModels

/-! Operational closure for the explicit-evidence finite scalar graph.
Unlike model-set idempotence alone, this also checks the detector's paired
atom representation. It does not establish general semantic knownness. -/
namespace Yulang.CommonRoleFiniteAssociatedStable
open CommonRoleFiniteAssociatedClosure CommonRoleFiniteAssociatedModels
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleCandidateStateFrontier (extend equality)

/-- Adding a whole scalar pair cannot create a different new scalar pair
by combining one old bound with a new bound. -/
theorem extend_evidence (s : State n) (slot target : Fin n)
    (head value : Inference.Base) :
    Evidence (extend s slot head).atoms target value ↔
      Evidence s.atoms target value ∨ (target = slot ∧ value = head) := by
  simp only [Evidence, extend, List.mem_append, equality, List.mem_cons, List.not_mem_nil,
    or_false, PresenceNormalForm.Atom.tyLe.injEq, Core.PresenceGeneration.TyTerm.var.injEq,
    Core.PresenceGeneration.TyTerm.base.injEq]
  constructor
  · rintro ⟨up, lo⟩
    rcases up with old | eq
    · rcases lo with old' | eq
      · exact Or.inl ⟨old, old'⟩
      · simp_all
    · simp_all
  · rintro (⟨up, lo⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl up, Or.inl lo⟩
    · simp

theorem emit_evidence (fs : List (Fact n)) (s : State n)
    (slot : Fin n) (head : Inference.Base) :
    Evidence (emit fs s).atoms slot head ↔
      Evidence s.atoms slot head ∨ (slot, head) ∈ fs := by
  induction fs generalizing s with
  | nil => simp [emit]
  | cons fact rest ih =>
    rcases fact with ⟨target, value⟩
    rw [emit, ih, extend_evidence]
    simp only [List.mem_cons, Prod.mk.injEq]
    exact or_assoc

/-- The operational detector gets exactly the derived facts after emission. -/
theorem run_evidence (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (slot : Fin n) (head : Inference.Base) :
    Evidence (run env roles wf p s).atoms slot head ↔
      Derives env roles wf p s (slot, head) := by
  rw [run, emit_evidence, saturate_exact]
  exact ⟨fun h => h.elim Derives.initial id, Or.inr⟩

/-- Re-starting the closure from its actual emitted ordinary state does not
create a new fact. This concerns arbitrary finite cycles, not fixed sweeps. -/
theorem derives_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) (fact : Fact n) :
    Derives env roles wf p (run env roles wf p s) fact ↔
      Derives env roles wf p s fact := by
  constructor
  · intro derived
    induction derived with
    | initial evidence => exact (run_evidence ..).mp evidence
    | identity same _ ih => exact .identity same ih
    | associated member _ computed ih => exact .associated member ih computed
  · intro derived
    induction derived with
    | initial evidence => exact .initial ((run_evidence ..).mpr (.initial evidence))
    | identity same _ ih => exact .identity same ih
    | associated member _ computed ih => exact .associated member ih computed

/-- Cache membership is a fixed point in the detector's concrete representation. -/
theorem cache_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) (fact : Fact n) :
    fact ∈ saturate env roles wf p (run env roles wf p s) ↔
      fact ∈ saturate env roles wf p s := by
  rw [saturate_exact, saturate_exact, derives_stable]

/-- All ordinary models are unchanged by running a second completed saturation. -/
theorem models_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (v : Fin n → Core.PresenceGeneration.Comp Common.model) :
    PresenceNormalForm.All Common.model v (run env roles wf p (run env roles wf p s)).atoms ↔
      PresenceNormalForm.All Common.model v (run env roles wf p s).atoms := by
  rw [run_models_exact, run_models_exact]
  simp only [derives_stable]
  exact and_self_right

end Yulang.CommonRoleFiniteAssociatedStable
