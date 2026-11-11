import Yulang.CommonRoleStructuralAssociatedClosure

/-! Check the completed mixed closure with the real ordinary solver, without
requiring structural closure atoms to fit the checked State grammar. A checked
state is reconstructed from the initial state and all paired scalar consequences.
The equivalence is over every assignment, not a chosen solver witness. -/
namespace Yulang.CommonRoleStructuralAssociatedSolver
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteAssociatedClosure (Occurrence Fact facts)
open CommonRoleCandidateStateFrontier (equality)
open CommonRoleStructuralAssociatedClosure

/-- Existing scalar equations, expressed independently of State construction. -/
theorem equality_models (slot : Fin n) (head : Inference.Base) (v : Fin n → Comp Common.model) :
    All Common.model v (equality slot head) ↔ Common.Equivalent (v slot).1 (.base head) := by
  simp [All,equality,Atom.Holds,Core.PresenceGeneration.TyTerm.eval,Common.model,Common.Equivalent]

/-- Only both bounds together are emitted, including when they were learned
through several alternating associated and structural ordinary steps. -/
def knownFacts (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (occurrences : List (Occurrence n))
    (seeds : List (Atom (Fin n))) : List (Fact n) :=
  let final := saturate env roles wf occurrences seeds
  (facts n).filter fun f => (equality f.1 f.2).all fun a => decide (a ∈ final)

theorem knownFacts_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (f : Fact n) :
    f ∈ knownFacts env roles wf occurrences seeds ↔
      ∀ a ∈ equality f.1 f.2, Derives env roles occurrences seeds a := by
  simp only [knownFacts,List.mem_filter,CommonRoleFiniteAssociatedClosure.facts_complete,
    true_and,List.all_eq_true,decide_eq_true_eq,saturate_exact env roles wf awf]

def completeState (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (occurrences : List (Occurrence n)) (initial : State n) : State n :=
  CommonRoleFiniteAssociatedModels.emit (knownFacts env roles wf occurrences initial.atoms) initial

/-- No approximated grammar check: emitted equations have the existing checked
State grammar, and represent exactly all final mixed-closure models. -/
theorem completeState_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model) :
    All Common.model v (completeState env roles wf occurrences initial).atoms ↔
      All Common.model v (saturate env roles wf occurrences initial.atoms) := by
  rw [completeState,CommonRoleFiniteAssociatedModels.emit_models]
  constructor
  · rintro ⟨initialModels,known⟩
    apply (models_exact env roles wf awf ..).mpr
    refine ⟨initialModels,?_⟩
    intro q member head output premises computed
    apply (equality_models q.output output v).mpr
    apply known (q.output,output)
    apply (knownFacts_exact env roles wf awf ..).mpr
    intro a eqs
    exact .associated q head output a member premises computed eqs
  · intro finalModels
    refine ⟨?_,?_⟩
    · intro a member
      exact finalModels a ((saturate_exact env roles wf awf ..).mpr (.seed a member))
    · intro f member
      apply (equality_models f.1 f.2 v).mp
      intro a eqs
      exact finalModels a ((saturate_exact env roles wf awf ..).mpr
        ((knownFacts_exact env roles wf awf ..).mp member a eqs))

/-- The actual ordinary solver accepts iff the independently specified final
mixed closure has a model. Rejection here is ordinary inconsistency only. -/
theorem solver_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) :
    CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences initial) = true ↔
      ∃ v : Fin n → Comp Common.model, ∀ a, Derives env roles occurrences initial.atoms a →
        a.Holds Common.model v := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  apply exists_congr
  intro v
  rw [completeState_models env roles wf awf]
  exact forall_congr' fun a => imp_congr_left (saturate_exact env roles wf awf ..)

/-- Complete state restarts do not create new derivations. All emitted paired
facts were already derived, and the initial constraints are retained. -/
theorem completeState_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (a) :
    Derives env roles occurrences (completeState env roles wf occurrences initial).atoms a ↔
      Derives env roles occurrences initial.atoms a := by
  have emit_atoms (fs : List (Fact n)) (s : State n) :
      (CommonRoleFiniteAssociatedModels.emit fs s).atoms =
        s.atoms ++ fs.flatMap (fun f => equality f.1 f.2) := by
    induction fs generalizing s with
    | nil => simp [CommonRoleFiniteAssociatedModels.emit]
    | cons f fs ih => simp only [CommonRoleFiniteAssociatedModels.emit,ih,
        CommonRoleCandidateStateFrontier.extend,List.flatMap_cons,List.append_assoc]
  have emitted := emit_atoms (knownFacts env roles wf occurrences initial.atoms) initial
  change Derives env roles occurrences (CommonRoleFiniteAssociatedModels.emit _ initial).atoms a ↔ _
  rw [emitted]
  constructor
  · intro h
    apply (derives_exact env roles wf awf ..).mp
    apply CommonRoleStructuralHornClosure.derives_cut (more := initial.atoms ++ _)
      (clauses := clauses env roles wf occurrences) _ ((derives_exact env roles wf awf ..).mpr h)
    intro b member
    apply (derives_exact env roles wf awf ..).mpr
    rcases List.mem_append.mp member with old | new
    · exact .seed b old
    · obtain ⟨f,member,eqs⟩ := List.mem_flatMap.mp new
      exact (knownFacts_exact env roles wf awf ..).mp member b eqs
  · intro h
    apply (derives_exact env roles wf awf ..).mp
    apply CommonRoleStructuralHornClosure.derives_cut (more := initial.atoms)
      (clauses := clauses env roles wf occurrences) _ ((derives_exact env roles wf awf ..).mpr h)
    intro b member
    exact .seed b (List.mem_append_left _ member)

end Yulang.CommonRoleStructuralAssociatedSolver
