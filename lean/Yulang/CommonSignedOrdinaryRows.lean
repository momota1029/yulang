import Yulang.CommonSignedGraphSolver
import Yulang.CommonRowTailInference

/-! Ordinary declared row constraints join the signed graph with the original
slot identities. No independent rows are merged during this conversion. -/
namespace Yulang.CommonSignedOrdinaryRows
open Common (Row)
open CommonSignedFlowFamily (Graph Edge Action)
open RowFlowSchemes (FlatConstraint FlatProblem)

variable {n : Nat}

def flatEdges (constraints : FlatProblem n) : List (Edge n) :=
  constraints.filterMap (fun | .flow source target => some ⟨source, target, .identity⟩ | .pure _ => none)

def flatPure (constraints : FlatProblem n) : List (Fin n) :=
  constraints.filterMap (fun | .flow _ _ => none | .pure target => some target)

theorem mem_flatEdges (constraints : FlatProblem n) (edge : Edge n) :
    edge ∈ flatEdges constraints ↔ edge.action = .identity ∧ .flow edge.source edge.target ∈ constraints := by
  simp only [flatEdges, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, same⟩
    cases constraint with
    | flow source target =>
      simp only [Option.some.injEq] at same
      subst edge
      exact ⟨rfl, member⟩
    | pure => cases same
  · rintro ⟨identity, member⟩
    refine ⟨.flow edge.source edge.target, member, ?_⟩
    cases edge with
    | mk source target action => cases identity; rfl

theorem mem_flatPure (constraints : FlatProblem n) (target : Fin n) :
    target ∈ flatPure constraints ↔ .pure target ∈ constraints := by
  simp only [flatPure, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, same⟩
    cases constraint with
    | flow => cases same
    | pure index => cases same; exact member
  · intro member
    exact ⟨.pure target, member, rfl⟩

def flatGraph (constraints : FlatProblem n) : Graph n := ⟨flatEdges constraints, flatPure constraints⟩

theorem flat_models_exact (constraints : FlatProblem n) (rows : Fin n → Row) :
    CommonSignedFlowFamily.Models (flatGraph constraints) rows ↔
      RowFlowSchemes.FlatModels Common.rowAlgebra constraints rows := by
  constructor
  · intro model constraint member
    cases constraint with
    | flow source target =>
      intro occurrence present
      exact model.1 ⟨source, target, .identity⟩
        ((mem_flatEdges constraints _).mpr ⟨rfl, member⟩) occurrence occurrence present rfl
    | pure target =>
      exact model.2 target ((mem_flatPure constraints target).mpr member)
  · intro model
    constructor
    · intro edge member source target present runs
      obtain ⟨action, listed⟩ := (mem_flatEdges constraints edge).mp member
      have same : source = target := by simpa [action, Action.run] using runs
      subst target
      exact model (.flow edge.source edge.target) listed source present
    · intro slot pure
      exact model (.pure slot) ((mem_flatPure constraints slot).mp pure)

def graphJoin (first last : Graph n) : Graph n := ⟨first.edges ++ last.edges, first.pure ++ last.pure⟩

theorem graphJoin_models (first last : Graph n) (rows : Fin n → Row) :
    CommonSignedFlowFamily.Models (graphJoin first last) rows ↔
      CommonSignedFlowFamily.Models first rows ∧ CommonSignedFlowFamily.Models last rows := by
  constructor
  · rintro ⟨edges, pure⟩
    exact ⟨⟨fun edge member => edges edge (List.mem_append_left _ member),
      fun slot member => pure slot (List.mem_append_left _ member)⟩,
      ⟨fun edge member => edges edge (List.mem_append_right _ member),
      fun slot member => pure slot (List.mem_append_right _ member)⟩⟩
  · rintro ⟨firstModel, lastModel⟩
    constructor
    · intro edge member
      exact (List.mem_append.mp member).elim (firstModel.1 edge) (lastModel.1 edge)
    · intro slot member
      exact (List.mem_append.mp member).elim (firstModel.2 slot) (lastModel.2 slot)

def augment (effect : CommonSignedGraphSolver.Scheme n)
    (constraints : List (CommonRowTailInference.RowConstraint n)) : CommonSignedGraphSolver.Scheme n :=
  ⟨graphJoin effect.graph (flatGraph (RowFlowSchemes.flatten (CommonRowTailInference.rowProblem constraints))), effect.heads⟩

theorem augment_models (effect : CommonSignedGraphSolver.Scheme n)
    (constraints : List (CommonRowTailInference.RowConstraint n)) (rows : Fin n → Row) :
    CommonSignedGraphSolver.Models (augment effect constraints) rows ↔
      CommonSignedGraphSolver.Models effect rows ∧ CommonRowTailInference.RowsHold constraints rows := by
  have original : CommonRowTailInference.RowsHold constraints rows ↔
      RowFlowSchemes.FlatModels Common.rowAlgebra
        (RowFlowSchemes.flatten (CommonRowTailInference.rowProblem constraints)) rows :=
    (CommonRowTailInference.rows_hold_iff constraints rows).trans
      (RowFlowSchemes.flatten_models_iff Common.rowAlgebra _
        (CommonRowTailInference.declared_rows_supported constraints) rows).symm
  change (CommonSignedFlowFamily.Models (graphJoin _ _) rows ∧ _) ↔ _
  rw [graphJoin_models, flat_models_exact, ← original]
  exact ⟨fun ⟨⟨effectModel, rowModel⟩, heads⟩ => ⟨⟨effectModel, heads⟩, rowModel⟩,
    fun ⟨⟨effectModel, heads⟩, rowModel⟩ => ⟨⟨effectModel, rowModel⟩, heads⟩⟩
end Yulang.CommonSignedOrdinaryRows
