import Yulang.GeneralDeclarativeNestedMaterial332
namespace Yulang.GeneralDeclarativeNativeMaterialBoundary465
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineMaterial331 (ordinary named protect)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeFootprint321 (stateNames equationNames)
open GeneralDeclarativeObserverGrowth330 (preserve backed_same)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)

theorem a_fresh_ordinary_allocation_has_no_older_available_source_origin
    {s : State} {p : Supported s done} {e : Equation}
    (made : e ∈ ordinary s a fixed used) :
    e ∉ (restriction p).equations := by
  intro claimed
  obtain ⟨_,stored,_⟩ := (backed_iff p e).mp claimed
  have old : e ∈ s.equations := p.ordinary stored
  have left_in : e.left ∈ s.equations.flatMap equationNames :=
    List.mem_flatMap.mpr ⟨e,old,List.mem_cons_self⟩
  have p1 : e.left ∈ stateNames s :=
    List.mem_append_right _ left_in
  exact GeneralDeclarativeInlineMaterial331.old_names_protected made
    (List.mem_append_left _ p1) rfl

/-- The actual old builder emits real ordinary rows. Even after
conservative support transport, its fresh rows are not authenticated
in the old available-origin relation. -/
theorem actual_old_assembly_keeps_allocations_and_available_sources_separate
    {s : State} {p : Supported s done}
    (bounds : Bounds s a) (printed : translate c i (normalize pat) = some code)
    (fromSource : Read (restriction p) .actual (.variable a.center) code used)
    (built : assemble s a fixed code used = some (out,spans)) :
    ∃ grown : GeneralDeclarativeGrowth327.Extends s out,
      (∀ m, Models out m ↔ Models (named s a fixed used) m) ∧
      ∀ e ∈ ordinary s a fixed used,
        e ∈ out.equations ∧ e ∉ (restriction (preserve p grown)).equations := by
  obtain ⟨retains,_,ordinaryRows,_,same⟩ :=
    GeneralDeclarativeNestedMaterial332.computed_frame bounds printed fromSource built
  exact ⟨retains.1,same,fun e stored => ⟨ordinaryRows stored,fun changed =>
    a_fresh_ordinary_allocation_has_no_older_available_source_origin (p := p) stored
      ((backed_same p retains.1 e).mp changed)⟩⟩

end Yulang.GeneralDeclarativeNativeMaterialBoundary465
