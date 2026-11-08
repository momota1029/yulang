import Yulang.CommonRoleFiniteAssociatedClosure

/-! Ordinary-state and order-independent model exactness of finite source
associated closure. No claim of general B4 classification or dynamic source
allocation is made. Initial scalar detection remains explicit-evidence only. -/
namespace Yulang.CommonRoleFiniteAssociatedModels
open CommonRoleFiniteAssociatedClosure
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleCandidateStateFrontier (extend)

/-- Emit each saturated equality exactly once. -/
def emit : List (Fact n) → State n → State n
  | [], s => s
  | (slot, head) :: rest, s => emit rest (extend s slot head)

theorem emit_models (fs : List (Fact n)) (s : State n)
    (v : Fin n → Comp Common.model) :
    All Common.model v (emit fs s).atoms ↔ All Common.model v s.atoms ∧
      ∀ fact ∈ fs, Common.Equivalent (v fact.1).1 (.base fact.2) := by
  induction fs generalizing s with
  | nil => simp [emit]
  | cons fact rest ih =>
    rcases fact with ⟨slot, head⟩
    rw [emit, ih, CommonRoleCandidateStateFrontier.extend_exact]
    simp only [List.forall_mem_cons]
    exact and_assoc

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : State n :=
  emit (saturate env roles wf p s) s

/-- Soundness/completeness for all ordinary assignments, not one solver model. -/
theorem run_models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n)
    (v : Fin n → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∀ fact,
        Derives env roles wf p s fact → Common.Equivalent (v fact.1).1 (.base fact.2) := by
  rw [run, emit_models]
  simp only [saturate_exact]

/-- Exact interface to the actual ordinary solver after finite saturation. -/
theorem solver_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    CommonRoleOpenPropagation.consistent (run env roles wf p s) = true ↔
      ∃ v : Fin n → Comp Common.model, All Common.model v s.atoms ∧
        ∀ fact, Derives env roles wf p s fact →
          Common.Equivalent (v fact.1).1 (.base fact.2) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_models_exact env roles wf p s)

/-- Source equality is semantic equality of identity tests plus the same
occurrences, allowing arbitrary reordering and duplication of occurrences. -/
def SameSource (p q : Source n) : Prop :=
  (∀ a b, p.identity a = p.identity b ↔ q.identity a = q.identity b) ∧
  (∀ occurrence, occurrence ∈ p.occurrences ↔ occurrence ∈ q.occurrences)

theorem derives_transport (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p q : Source n) (s : State n)
    (same : SameSource p q) (fact : Fact n)
    (derived : Derives env roles wf p s fact) : Derives env roles wf q s fact := by
  induction derived with
  | initial evidence => exact .initial evidence
  | identity equal _ ih => exact .identity ((same.1 _ _).mp equal) ih
  | associated member _ computed ih => exact .associated ((same.2 _).mp member) ih computed

/-- Arbitrary sibling permutation preserves all derived facts. -/
theorem derives_order_independent (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p q : Source n) (s : State n)
    (same : SameSource p q) (fact : Fact n) :
    Derives env roles wf p s fact ↔ Derives env roles wf q s fact :=
  ⟨derives_transport env roles wf p q s same fact,
   derives_transport env roles wf q p s
     ⟨fun _ _ => (same.1 _ _).symm, fun _ => (same.2 _).symm⟩ fact⟩

/-- Model-set equality, not syntactic equality of the emitted atom list. -/
theorem models_order_independent (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p q : Source n) (s : State n)
    (same : SameSource p q) (v : Fin n → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v (run env roles wf q s).atoms := by
  rw [run_models_exact, run_models_exact]
  simp only [derives_order_independent env roles wf p q s same]

/-- Executable fact closure is independent of where occurrence enumeration. -/
theorem cache_order_independent (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p q : Source n) (s : State n)
    (same : SameSource p q) (fact : Fact n) :
    fact ∈ saturate env roles wf p s ↔ fact ∈ saturate env roles wf q s := by
  rw [saturate_exact, saturate_exact]
  exact derives_order_independent env roles wf p q s same fact

end Yulang.CommonRoleFiniteAssociatedModels
