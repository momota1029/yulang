import Yulang.GeneralDictionaryDefaultBodyTransport209
import Yulang.GeneralDictionaryDefaultConfiguration209

set_option backward.isDefEq.respectTransparency false

/-! Point arguments determine every input center semantically. This remains
valid after reobservation without equality of cached reports or center names.
It concerns defaults only; explicit-body binder transport remains separate. -/
namespace Yulang.GeneralDictionaryDefaultPointTransport209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultExpression209
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {model : GeneralNominalCommonBridge.Assignment}

 theorem centers_equivalent (first last : Site roles)
    (same : first.occurrence = last.occurrence)
    (point : ∀ index, (first.occurrence.demand.arguments index).1 = (first.occurrence.demand.arguments index).2)
    (one : first.Holds model) (two : last.Holds model) (index : Nat) :
    Equivalent (model ((List.ofFn first.center)[index]?.getD 0)).1
      (model ((List.ofFn last.center)[index]?.getD 0)).1 := by
  rcases first with ⟨first,a⟩
  rcases last with ⟨last,b⟩
  dsimp at same
  subst last
  by_cases within : index < (roles first.demand.role).arity
  · simp only [List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some]
    have firstFits := one ⟨index,within⟩
    have lastFits := two ⟨index,within⟩
    change Subtype _ _ ∧ Subtype _ _ at firstFits lastFits
    rw [← point ⟨index,within⟩] at firstFits lastFits
    exact ⟨subtype_trans firstFits.2 lastFits.1,subtype_trans lastFits.2 firstFits.1⟩
  · simp only [List.getElem?_ofFn,within,↓reduceDIte,Option.getD_none]
    exact equivalent_refl _

 theorem default_transport {first last : Plan roles}
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (same : first.input.occurrence = last.input.occurrence)
    (point : ∀ index, (first.input.occurrence.demand.arguments index).1 = (first.input.occurrence.demand.arguments index).2)
    (one : first.input.Holds model) (two : last.input.Holds model) :
    BodyHolds first target model (.default role name term) ↔
      BodyHolds last target model (.default role name term) := by
  have compile := GeneralDictionaryDefaultBodyTransport209.compile_equal constructors interpretation (.default role name term)
  cases translated : compileBody first (.default role name term) with
  | none =>
      have other : compileBody last (.default role name term) = none := compile.symm.trans translated
      simp [BodyHolds,bodySchema,translated,other,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
  | some expression =>
      apply GeneralDictionaryDefaultBodyTransport209.body_holds_iff translated (compile.symm.trans translated)
      intro index _
      exact centers_equivalent first.input last.input same point one two index

 theorem stored_default_output {state : State roles} {current historical : Plan roles}
    (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
    (present : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (current.input.occurrence.demand.arguments index).1 =
      (current.input.occurrence.demand.arguments index).2)
    (valid : Models state model)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus)
    (found : GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name =
      some (.default role name term)) :
    BodyHolds current output.target model (.default role name term) := by
  have old := GeneralDictionaryDefaultRecorded208.current_class reachable present valid
  have oldEquation := old.1 output (occurrence.symm ▸ member) (.default role name term) (declaration ▸ found)
  have configuration : current.packet.registry.constructors = historical.packet.registry.constructors ∧
      current.packet.context.interpretation = historical.packet.context.interpretation := by
    obtain ⟨start,initial,path⟩ := reachable
    have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
    obtain ⟨context,labels,source,pointSource,ground,coverage,rfl⟩ := compiled
    have built := GeneralDictionaryDefaultTrace208.built_trace path
    have stored := GeneralDictionaryDefaultConfiguration209.stored built present
    exact ⟨congrArg Registry.constructors (frame.registry_eq.trans stored.1.symm),
      ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
        (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans stored.2.2.1.symm⟩
  have same := current.input_exact.trans (frame.occurrence_eq.trans (occurrence.symm.trans historical.input_exact.symm))
  exact (default_transport configuration.1 configuration.2 same point
    (valid.2.2.2.1 current.input frame.center_recorded)
    (GeneralNominalCenteredHeadMatStepPackets.head_equations (valid.2.2.2.2.1 historical present)).1).mpr oldEquation

end Yulang.GeneralDictionaryDefaultPointTransport209
