import Yulang.CommonDeclaredNominalSlots
import Yulang.CommonBoundRefSolvedExact
import Yulang.CommonEffectCapturedCompilation

/-!
# Existing Common source families with declared nominal slot constraints

The finite inspector's ordinary atoms are appended to the original clause.
The original Common graph compiler and solved worklist then operate on the
whole problem once. Original source rows, original value slots and all their
sharing are retained. Every returned parameter is unrestricted.

This is a clause-boundary connection for nominal metadata constraints on
Common arguments. It does not introduce nominal source expressions or claim
the declaration-aware recursive nominal carrier, construction/cast or EOF
rules have been implemented.
-/

namespace Yulang.CommonDeclaredNominalSourceFamily

open Common (Ty Row Equivalent)
open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All Clause normalise)
open CommonDeclaredNominalInspection (Registry)
open CommonDeclaredNominalSlots (Comparison inspectAll)

variable {slots : Nat}

def compile (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) : Option (List (Atom (Fin slots))) :=
  (inspectAll registry comparisons).map (original ++ ·)

def Models (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (assignment : Fin slots → Comp Common.model) : Prop :=
  All Common.model assignment original ∧ CommonDeclaredNominalSlots.Models registry comparisons assignment

theorem compile_models_exact (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (assignment : Fin slots → Comp Common.model) :
    CommonNominalConstraints.Satisfied assignment (compile registry original comparisons) ↔
      Models registry original comparisons assignment := by
  have exactInspection := CommonDeclaredNominalSlots.inspect_all_exact registry comparisons assignment
  cases found : inspectAll registry comparisons <;>
    simp_all [compile, Models, CommonNominalConstraints.Satisfied, PresenceNormalForm.all_append]

theorem compiled_grammar (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (atoms : List (Atom (Fin slots))) (compiled : compile registry original comparisons = some atoms) :
    PresenceGeneratedChildGrammar.GoodAtoms atoms ∧ PresenceGeneratedWidth.WidthAtoms atoms ∧
      PresenceSourceConstraintSupport.GoodAtoms atoms := by
  obtain ⟨added, returned, rfl⟩ := Option.map_eq_some_iff.mp compiled
  obtain ⟨newChild, newWidth, newRows⟩ :=
    CommonDeclaredNominalSlots.inspect_all_grammar registry comparisons added returned
  exact ⟨child.append newChild, width.append newWidth, rows.append newRows⟩

/-- Only actual finite syntax and the existing solved scheme are stored. -/
structure Scheme (slots : Nat) where
  atoms : List (Atom (Fin slots))
  solved : CommonBoundRefSolved.Scheme (CommonPresenceConstraintGraph.splitAtoms atoms).pool

abbrev Scheme.Parameters (scheme : Scheme slots) := scheme.solved.Parameters

def Scheme.instantiate (scheme : Scheme slots) (rowParameters : Fin slots → Row)
    (parameters : scheme.Parameters) : Fin slots → Comp Common.model :=
  (CommonPresenceConstraintGraph.compile scheme.atoms).readback
    (scheme.solved.instantiateRows rowParameters)
    (scheme.solved.instantiateValues rowParameters parameters)

def solve (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) : List (Scheme slots) :=
  match compile registry original comparisons with
  | none => []
  | some atoms => (CommonBoundRefSolved.solveAll atoms).map (fun solved => ⟨atoms, solved⟩)

theorem mem_solve (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (scheme : Scheme slots) :
    scheme ∈ solve registry original comparisons ↔
      ∃ atoms, compile registry original comparisons = some atoms ∧
        ∃ solved ∈ CommonBoundRefSolved.solveAll atoms, scheme = ⟨atoms, solved⟩ := by
  cases found : compile registry original comparisons <;> simp [solve, found]
  case some atoms =>
    constructor
    · rintro ⟨solved, returned, rfl⟩
      exact ⟨solved, returned, rfl⟩
    · rintro ⟨solved, returned, rfl⟩
      exact ⟨solved, returned, rfl⟩

/-- All rows are equal literally; all original value components are
recovered in the independent Common demand equivalence. -/
def AssignmentEquivalent (first last : Fin slots → Comp Common.model) : Prop :=
  (∀ index, (first index).2 = (last index).2) ∧
    ∀ index, Equivalent (first index).1 (last index).1

theorem rows_eval_congr (first last : Fin slots → Comp Common.model)
    (same : ∀ index, (first index).2 = (last index).2) (term : RowTerm (Fin slots)) :
    term.eval Common.model first = term.eval Common.model last := by
  induction term <;> simp_all [RowTerm.eval]

theorem atoms_congr (atoms : List (Atom (Fin slots))) (first last : Fin slots → Comp Common.model)
    (same : AssignmentEquivalent first last) :
    All Common.model first atoms ↔ All Common.model last atoms := by
  apply forall_congr'
  intro atom
  apply forall_congr'
  intro _
  cases atom with
  | tyLe source target =>
      have sourceSame := CommonEffectCapturedCompilation.term_congr source first last same.1 same.2
      have targetSame := CommonEffectCapturedCompilation.term_congr target first last same.1 same.2
      exact ⟨fun below => Common.subtype_trans sourceSame.2 (Common.subtype_trans below targetSame.1),
        fun below => Common.subtype_trans sourceSame.1 (Common.subtype_trans below targetSame.2)⟩
  | rowLe source target =>
      simp only [Atom.Holds, rows_eval_congr first last same.1]

theorem models_congr (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (first last : Fin slots → Comp Common.model)
    (same : AssignmentEquivalent first last) :
    Models registry original comparisons first ↔ Models registry original comparisons last := by
  rw [← compile_models_exact, ← compile_models_exact]
  unfold CommonNominalConstraints.Satisfied
  exact exists_congr fun atoms => and_congr Iff.rfl (atoms_congr atoms first last same)

/-- No source-grammar or semantic premise is imposed on the parameters.
Every actual returned scheme satisfies both the original source clause and
all declaration-aware nominal comparisons, at their original shared slots. -/
theorem all_parameters_models (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (scheme : Scheme slots)
    (returned : scheme ∈ solve registry original comparisons)
    (rowParameters : Fin slots → Row) (parameters : scheme.Parameters) :
    Models registry original comparisons (scheme.instantiate rowParameters parameters) := by
  obtain ⟨atoms, compiled, solved, member, rfl⟩ :=
    (mem_solve registry original comparisons scheme).mp returned
  apply (compile_models_exact registry original comparisons _).mp
  refine ⟨atoms, compiled, ?_⟩
  exact CommonPresenceConstraintGraph.compile_atoms_reflects atoms _ _
    (CommonBoundRefSolved.all_parameters_models atoms solved member rowParameters parameters)

/-- The syntactic premises apply only to the original clause. All syntax
premises for the added nominal constraints are discharged internally.
The source-generated corollaries below discharge the original premises too. -/
theorem solve_all_instances_exact (registry : Registry) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    Models registry original comparisons assignment ↔
      ∃ scheme ∈ solve registry original comparisons,
        ∃ rowParameters : Fin slots → Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment := by
  constructor
  · intro model
    obtain ⟨atoms, compiled, accepted⟩ :=
      (compile_models_exact registry original comparisons assignment).mpr model
    obtain ⟨newChild, newWidth, newRows⟩ :=
      compiled_grammar registry original comparisons child width rows atoms compiled
    obtain ⟨values, graphModel, originalValues⟩ :=
      (CommonPresenceConstraintGraph.compile_atoms_exact atoms assignment).mp accepted
    obtain ⟨solved, member, rowParameters, parameters, sameRows, sameValues⟩ :=
      (CommonBoundRefSolved.solve_all_instances_exact atoms newChild newWidth newRows _ values).mp graphModel
    let scheme : Scheme slots := ⟨atoms, solved⟩
    refine ⟨scheme, (mem_solve registry original comparisons scheme).mpr
      ⟨atoms, compiled, solved, member, rfl⟩, rowParameters, parameters, ?_, ?_⟩
    · intro index
      exact congrFun sameRows index
    · intro index
      have recovered := sameValues ((CommonPresenceConstraintGraph.compile atoms).input index)
      have original := congrArg Prod.fst (congrFun originalValues index)
      change Equivalent _ (assignment index).1
      rw [← original]
      exact recovered
  · rintro ⟨scheme, returned, rowParameters, parameters, same⟩
    exact (models_congr registry original comparisons _ assignment same).mp
      (all_parameters_models registry original comparisons scheme returned rowParameters parameters)

/-- Every clause ACTUALLY generated from the original source expression,
every finite table/comparison list and every independent original assignment.
No support, width, success, fuel or residual-model premise remains. -/
theorem generated_models_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (registry : Registry) (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models registry clause.pack comparisons assignment ↔
      ∃ scheme ∈ solve registry clause.pack comparisons,
        ∃ rowParameters : Fin (clause.locals + 1) → Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact registry clause.pack comparisons
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) assignment

theorem generated_core_models_exact (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (registry : Registry) (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models registry clause.pack comparisons assignment ↔
      ∃ scheme ∈ solve registry clause.pack comparisons,
        ∃ rowParameters : Fin (clause.locals + 1) → Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact registry clause.pack comparisons
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated)
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause generated) assignment

end Yulang.CommonDeclaredNominalSourceFamily
