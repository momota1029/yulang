import Yulang.GeneralVersionedAliasCenters312
import Yulang.GeneralNominalHeadTestSemantic186

set_option backward.isDefEq.respectTransparency false
/-! Literal report/endpoint equality is unnecessary: a checked historical
head supplies actual tests and shared captures at current alias centers. -/
namespace Yulang.GeneralVersionedAliasReadback312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalOriginTerms (Same Head)
open GeneralNominalMaterialization (Use)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultIdentityCenters214 (CentersSame)
open GeneralNominalVersionedPlans231 (SchemaHolds)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
  {m : Assignment} {past now : Plan roles}

theorem configuration
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (history : past ∈ state.plans) (current : now.packet.context = state.core.erased.current.context) :
    now.packet.context.state.constructors = past.packet.context.state.constructors ∧
    now.packet.context.interpretation = past.packet.context.interpretation := by
  have old := GeneralVersionedSiteOrigins312.stored_current_config path history
  rw [current]
  exact ⟨old.2.1.symm,old.2.2.symm⟩

theorem centers
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (history : past ∈ state.plans) (registered : now.input ∈ state.core.sites)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (valid : Models state m) : CentersSame m now.input past.input := by
  obtain ⟨context,built⟩ := GeneralVersionedSiteOrigins312.reached path
  apply GeneralVersionedAliasCenters312.same_alias checked path valid registered (built.input past history)
  simpa only [now.input_exact,past.input_exact] using alias

theorem actual_of_centers
    (decl : now.packet.declaration = past.packet.declaration)
    (constructors : now.packet.context.state.constructors = past.packet.context.state.constructors)
    (interpretation : now.packet.context.interpretation = past.packet.context.interpretation)
    (same : CentersSame m now.input past.input)
    (held : SchemaHolds past past.headSchema m)
    (entry : Use) (present : entry ∈ now.headSchema.variables) :
    Same m entry.origin (.source (past.binder entry.name)) := by
  obtain ⟨other,found,nameEq,_,related⟩ := GeneralNominalHeadSchemaSemantic186.head_correspondence
    now past decl constructors interpretation same entry present
  have actual := GeneralNominalHeadSchemaNames186.head_actual past other found
  have readback : Same m other.origin (.source (past.binder other.name)) := by
    simpa only [actual,ite_true,GeneralNominalVersionedFrame231.binder_eq] using held.2 other found
  rw [nameEq]
  exact GeneralNominalHeadSchemaSemantic186.related_holds
    (term := .leaf (.source (past.binder other.name))) (GeneralNominalHeadSchemaSemantic186.related_symm related) readback

theorem tests_of_centers
    (decl : now.packet.declaration = past.packet.declaration)
    (constructors : now.packet.context.state.constructors = past.packet.context.state.constructors)
    (interpretation : now.packet.context.interpretation = past.packet.context.interpretation)
    (same : CentersSame m now.input past.input)
    (held : SchemaHolds past past.headSchema m)
    (entry : Origin × Test) (present : entry ∈ now.headSchema.tests) : Head m entry.1 entry.2 := by
  obtain ⟨other,found,testEq,related⟩ := GeneralNominalHeadTestSemantic186.head_tests now past decl
    constructors interpretation same entry present
  rw [testEq]
  exact GeneralNominalHeadTestSemantic186.related_head (GeneralNominalHeadSchemaSemantic186.related_symm related)
    (held.1 other found)

/-- The same live assignment satisfies the current head tests and relates
all current actual captures to their historical binders. Neither assertion
assumes that the current head report is finished or already prepared. -/
theorem readback
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (history : past ∈ state.plans) (registered : now.input ∈ state.core.sites)
    (current : now.packet.context = state.core.erased.current.context)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (decl : now.packet.declaration = past.packet.declaration)
    (valid : Models state m) :
    (∀ entry ∈ now.headSchema.tests, Head m entry.1 entry.2) ∧
    ∀ entry ∈ now.headSchema.variables, Same m entry.origin (.source (past.binder entry.name)) := by
  obtain ⟨constructors,interpretation⟩ := configuration path history current
  have same := centers checked path history registered alias valid
  have held := (GeneralNominalVersionedDiagnostic232.head_equations (valid.2.1 past history)).2.2
  exact ⟨tests_of_centers decl constructors interpretation same held,
    actual_of_centers decl constructors interpretation same held⟩

end Yulang.GeneralVersionedAliasReadback312
