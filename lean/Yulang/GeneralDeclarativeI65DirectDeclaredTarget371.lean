import Yulang.GeneralDeclarativeI65SourceBodyProduction371

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeProducedNames325 (allocation_exact output table)
open GeneralDeclarativeFrameReadback325 (placeById sourceNames)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Declaration Clause DeclarationChecked)

theorem unique_clause_id_keeps_written_row {xs : List Clause} {c : Clause}
    (unique : (xs.map Clause.id).Nodup) (appears : c ∈ xs) :
    xs.find? (fun d => d.id == c.id) = some c := by
  induction xs with
  | nil => cases appears
  | cons front tail ih =>
    obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp appears with rfl|later
    · simp
    · have notFront : front.id ≠ c.id := fun same => fresh
        (same.symm ▸ List.mem_map.mpr ⟨c,later,rfl⟩)
      simpa [notFront] using ih tailUnique later

/-- A direct output binder reuses the **producing** source row's
exact placement, which need not be the consuming clause's target
allocation or an equal model value at some other name. -/
theorem direct_output_target_uses_declaring_equation {decl : Declaration}
    (checked : DeclarationChecked constructors roles decl)
    (place : Placement) (base : Nat → GeneralDeclarativeWhere319.Capture)
    {binder : GeneralDeclarations.OutputBinder} (listed : binder ∈ decl.outputBinders)
    {consumer : Clause} {read : GeneralDeclarations.Equation}
    (sameRhs : normalize read.rhs = .var binder.name) :
    ∃ author ∈ decl.requirements, author.id = binder.clause ∧
      ∃ written ∈ author.outputs, written.id = binder.equation ∧
        (useOutput decl (sourceNames decl place base) (place.targets consumer) read).target =
          place.targets author written.id := by
  obtain ⟨author,there,sourceKey,written,writtenThere,writtenKey,_⟩ := checked.produced binder listed
  have seen : binder.name ∈ decl.outputNames := List.mem_map.mpr ⟨binder,listed,rfl⟩
  have actual := unique_clause_id_keeps_written_row checked.identified.1 there
  refine ⟨author,there,sourceKey,written,writtenThere,writtenKey,?_⟩
  simp only [useOutput,GeneralDeclarationDemands.outputTarget,sameRhs,seen, ↓reduceIte,
    Names.old,sourceNames,table,output,
    allocation_exact checked.identified.2.2.2.1 listed,Option.getD_some,
    placeById,← sourceKey,actual,Option.map_some,← writtenKey]

end Yulang.GeneralDeclarativeI65
