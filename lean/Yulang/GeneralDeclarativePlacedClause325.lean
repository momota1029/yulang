import Yulang.GeneralDeclarativeFrameReadback325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlacedClause325
open GeneralDeclarations (Clause Declaration DeclarationChecked)
open GeneralDeclarativeFrameReadback325 (placeById sourceNames)
open GeneralDeclarativeProducedNames325 (generated)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeSourceEmission322 (useOutput)

theorem unique_clause {clauses : List Clause} (identified : (clauses.map Clause.id).Nodup)
    (belongs : c ∈ clauses) : (clauses.find? fun x => x.id == c.id) = some c := by
  induction clauses with
  | nil => cases belongs
  | cons next rest ih =>
    rcases List.mem_cons.mp belongs with rfl|later
    · simp
    · obtain ⟨unique,less⟩ := List.nodup_cons.mp identified
      have different : next.id ≠ c.id := fun h =>
        unique (h ▸ (List.mem_map.mpr ⟨c,later,rfl⟩))
      simp [different,ih less later]

theorem at_actual_clause {place : Placement} (checked : DeclarationChecked c roles decl)
    (belongs : clause ∈ decl.requirements) :
    placeById decl place clause.id eq = place.targets clause eq := by
  unfold placeById
  rw [unique_clause checked.identified.1 belongs]
  rfl

/-- The canonical table ties a produced output to the actual clause and
equation, even when other clauses ask the same associated output name. -/
theorem bound_to_producing_clause {place : Placement} (checked : DeclarationChecked c roles decl)
    (belongs : binder ∈ decl.outputBinders) :
    ∃ clause ∈ decl.requirements, clause.id = binder.clause ∧
      ∃ eq ∈ clause.outputs, eq.id = binder.equation ∧
        (useOutput decl (sourceNames decl place base) (place.targets clause) eq).target =
          place.targets clause eq.id := by
  obtain ⟨cl,whereClause,sameClause,eq,whereEq,sameEq,computed⟩ :=
    generated (placed := placeById decl place) (resolved := base) checked belongs
  have same : placeById decl place cl.id = place.targets cl := funext
    (fun x => at_actual_clause (eq := x) checked whereClause)
  exact ⟨cl,whereClause,sameClause,eq,whereEq,sameEq,by simpa only [sourceNames,same] using computed⟩

end Yulang.GeneralDeclarativePlacedClause325
