import Yulang.GeneralDictionaryDefaultSchema208

namespace Yulang.GeneralDictionaryDefaultProvenance208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralDictionaryDefaultSchema208
variable {roles : Roles.RoleDecls} {state : GeneralNominalCenteredSteps.State roles}
  {root : Occurrence roles} {plan : Plan roles} {output : GeneralSourceState.Output}

theorem supplied_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (supplied : Supplies roles plan.packet.declaration output.name body) :
    Entry.mk output (some body) ∈ entries state root plan := by
  have found := (lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 _ _).mpr supplied
  exact mem_entries.mpr ⟨output,member,by rw [found]⟩

theorem explicit_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (present : equation ∈ plan.packet.declaration.associated)
    (named : equation.name = output.name) :
    Entry.mk output (some (.explicit equation)) ∈ entries state root plan :=
  supplied_entry member (.explicit equation present named)

theorem default_entry
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (absent : ∀ equation ∈ plan.packet.declaration.associated, equation.name ≠ output.name)
    (declared : (roles plan.packet.declaration.role).assoc output.name = some (some rhs)) :
    Entry.mk output (some (.default plan.packet.declaration.role output.name rhs)) ∈ entries state root plan :=
  supplied_entry member (.default rhs absent declared)

/-- An explicit equation excludes a default-provenance entry for the same
requested output, even if the role declares that default. -/
theorem override_excludes_default
    (present : equation ∈ plan.packet.declaration.associated)
    (named : equation.name = output.name) :
    Entry.mk output (some (.default role name rhs)) ∉ entries state root plan := by
  intro member
  have supplied := entry_provenance member rfl
  have same := supplies_unique roles plan.packet.declaration
    plan.packet.checked.identified.2.2.1 output.name (.explicit equation) (.default role name rhs)
    (.explicit equation present named) supplied
  cases same

theorem schema_enforces_supplied
    (schema : SchemaHolds state root plan model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root)
    (supplied : Supplies roles plan.packet.declaration output.name body) :
    GeneralNominalCenteredHeadMatEffects.BodyHolds plan output.target model body :=
  schema.2.1 _ (supplied_entry member supplied) body rfl

end Yulang.GeneralDictionaryDefaultProvenance208
