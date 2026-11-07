import Yulang.CommonNominalAtomicPool

/-!
# Actual full source formulas as finite shared mixed pool problems

The real normalizer and packed allocator allocate all original binders. Each
returned problem contains only the local count and actual graph syntax.
Every original ambient computation is read back literally, including rows;
every original source/model branch is preserved in both directions.

This finite-generation theorem does not solve arbitrary bounds or impose
their Models predicate on a purported free parameter family.
-/

namespace Yulang.CommonNominalFormulaPool

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)
open CommonNominalFieldTemplates (Formula)
open CommonNominalFieldNormalForm (Clause normalise)

structure Problem (ambient : Nat) where
  locals : Nat
  graph : CommonNominalAtomicGraph.Graph (locals + ambient)

def Problem.Models (problem : Problem ambient) (assignment : Fin ambient → Comp model)
    (rows : Fin (problem.locals + ambient) → Row)
    (values : Fin (problem.graph.template.nodes + (problem.locals + ambient)) → Ty) : Prop :=
  CommonNominalAtomicPool.Models problem.graph rows values ∧
    ∀ index, CommonNominalAtomicPool.readback problem.graph rows values (Fin.natAdd problem.locals index) = assignment index

def compile (formula : Formula (Fin ambient)) : List (Problem ambient) :=
  (normalise formula).map fun clause => ⟨clause.locals, CommonNominalAtomicGraph.compile clause.pack⟩

/-- Exact generation of real finite mixed-pool problems for every original
full formula. No solved-family, support, source grammar or fuel premise. -/
theorem compile_exact (formula : Formula (Fin ambient)) (assignment : Fin ambient → Comp model) :
    formula.Models assignment ↔ ∃ problem ∈ compile formula,
      ∃ rows values, problem.Models assignment rows values := by
  constructor
  · intro original
    obtain ⟨clause, clauseReturned, clauseModel⟩ := (CommonNominalFieldNormalForm.normalise_exact assignment formula).mpr original
    obtain ⟨packed, ambientSame, atomsModel⟩ := (clause.pack_exact assignment).mp clauseModel
    obtain ⟨internal, poolModel⟩ := (CommonNominalAtomicPool.compile_atoms_exact clause.pack packed).mp atomsModel
    let graph := CommonNominalAtomicGraph.compile clause.pack
    let problem : Problem ambient := ⟨clause.locals, graph⟩
    let rows : Fin (clause.locals + ambient) → Row := fun index => (packed index).2
    let values := CommonNominalTemplateLowering.values internal (fun index => (packed index).1)
    refine ⟨problem, List.mem_map.mpr ⟨clause, clauseReturned, rfl⟩, rows, values, poolModel, ?_⟩
    have recovered := CommonNominalAtomicPool.readback_original graph packed internal
    intro index
    exact (congrFun recovered (Fin.natAdd clause.locals index)).trans (ambientSame index)
  · rintro ⟨problem, returned, rows, values, poolModel, ambientSame⟩
    obtain ⟨clause, clauseReturned, rfl⟩ := List.mem_map.mp returned
    have atomsModel := CommonNominalAtomicPool.all_pool_models_recover clause.pack rows values poolModel
    have clauseModel := (clause.pack_exact assignment).mpr ⟨_, ambientSame, atomsModel⟩
    exact (CommonNominalFieldNormalForm.normalise_exact assignment formula).mp ⟨clause, clauseReturned, clauseModel⟩

theorem all_returned_models_recover (formula : Formula (Fin ambient)) (assignment : Fin ambient → Comp model)
    (problem : Problem ambient) (returned : problem ∈ compile formula)
    (rows : Fin (problem.locals + ambient) → Row)
    (values : Fin (problem.graph.template.nodes + (problem.locals + ambient)) → Ty)
    (originalModel : problem.Models assignment rows values) : formula.Models assignment :=
  (compile_exact formula assignment).mpr ⟨problem, returned, rows, values, originalModel⟩

end Yulang.CommonNominalFormulaPool
