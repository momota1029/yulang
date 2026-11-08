import Yulang.CommonRoleCandidateConstraints
import Yulang.CommonRigidHeadInspection

/-!
An actual solver example for one repeated head variable. Each captured
interval can be consistent on its own, but their cross constraints cannot
both hold when the first lower is `int` and the second upper is `str`.
This is an ordinary-constraint example, not a whole role-resolution result.
-/
namespace Yulang.CommonRoleCandidateConstraintExamples

open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleCandidateConstraints

def original : List (Atom (Fin 4)) :=
  [.tyLe (.base .int) (.var 0), .tyLe (.var 1) (.base .int),
   .tyLe (.base .str) (.var 2), .tyLe (.var 3) (.base .str)]

def repeated : Bindings 4 := [(0, (0, 1)), (0, (2, 3))]

def separateAssignment (slot : Fin 4) : Comp Common.model :=
  Comp.pure Common.model (if slot.val < 2 then .base .int else .base .str)

theorem individual_intervals_consistent :
    All Common.model separateAssignment original ∧
      Common.Subtype (separateAssignment 0).1 (separateAssignment 1).1 ∧
      Common.Subtype (separateAssignment 2).1 (separateAssignment 3).1 := by
  have three : ¬ (3 : Fin 4).val < 2 := by decide
  simp [All, original, separateAssignment, Atom.Holds, TyTerm.eval, Comp.pure, Common.model,
    Common.subtype_refl, three]

theorem generated_cross_checks :
    generate repeated = [.tyLe (.var 0) (.var 1), .tyLe (.var 0) (.var 3),
      .tyLe (.var 2) (.var 1), .tyLe (.var 2) (.var 3)] := rfl

theorem original_grammar :
    PresenceGeneratedChildGrammar.GoodAtoms original ∧ PresenceGeneratedWidth.WidthAtoms original ∧
      PresenceSourceConstraintSupport.GoodAtoms original := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    simp only [original, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  · intro source target member tail needed
    simp only [original, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal | equal <;> cases equal <;> cases needed
  · intro atom member
    simp only [original, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial

theorem cross_inconsistent :
    ¬ ∃ assignment : Fin 4 → Comp Common.model,
      All Common.model assignment original ∧ Compatible repeated assignment := by
  rintro ⟨assignment, model, compatible⟩
  have first := model (.tyLe (.base .int) (.var 0)) (by simp [original])
  have last := model (.tyLe (.var 3) (.base .str)) (by simp [original])
  have cross := compatible 0 (by decide) (0, 1) (by decide) (2, 3) (by decide)
  have impossible : Common.Subtype (.base .int) (.base .str) :=
    Common.subtype_trans first (Common.subtype_trans cross last)
  cases (CommonRigidHeadInspection.base_iff .int .str).mp impossible

theorem solver_rejects_cross_conflict : solve original repeated = [] :=
  (solve_empty_exact original repeated original_grammar.1 original_grammar.2.1 original_grammar.2.2).mpr
    cross_inconsistent

/-- The repeated capture comes from the actual graph inspector, with each
captured node mapped to its original lower/upper slot pair. -/
def graph : CommonRoleRegularGraph.Graph 3 := fun node =>
  if node = 0 then .structural 0 [1, 2] else if node = 1 then .scalar 0 else .scalar 1

def slotBounds (node : Fin 3) : Fin 4 × Fin 4 :=
  if node = 2 then (2, 3) else (0, 1)

def head : CommonRoleGraphInspection.Pattern :=
  .structural 0 [.variable 0, .variable 0]

theorem prepared_bindings : (prepare original slotBounds graph head 0).bindings = repeated := by
  decide +kernel

theorem inspected_candidate_conflict : (prepare original slotBounds graph head 0).schemes = [] := by
  change solve original (prepare original slotBounds graph head 0).bindings = []
  rw [prepared_bindings]
  exact solver_rejects_cross_conflict

end Yulang.CommonRoleCandidateConstraintExamples
