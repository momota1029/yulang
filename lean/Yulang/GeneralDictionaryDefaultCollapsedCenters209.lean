import Yulang.GeneralDictionaryDefaultSemanticReplay209

set_option backward.isDefEq.respectTransparency false

/-! A syntactic point is sufficient but not necessary. Intervals collapsed in
one model also identify their centers semantically. Unrestricted intervals do
not have this property (TransportExamples209). No source names are identified. -/
namespace Yulang.GeneralDictionaryDefaultCollapsedCenters209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatEffects CommonNominalFullCarrier
open GeneralDictionaryDefaultSemanticReplay209 (recenter)
variable {roles : Roles.RoleDecls} {model : GeneralNominalCommonBridge.Assignment}

 theorem centers_equivalent (first last : Site roles)
    (same : first.occurrence = last.occurrence)
    (collapsed : ∀ index, Equivalent
      (model (first.occurrence.demand.arguments index).1).1
      (model (first.occurrence.demand.arguments index).2).1)
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
    exact ⟨subtype_trans firstFits.2 (subtype_trans (collapsed ⟨index,within⟩).2 lastFits.1),
      subtype_trans lastFits.2 (subtype_trans (collapsed ⟨index,within⟩).2 firstFits.1)⟩
  · simp only [List.getElem?_ofFn,within,↓reduceDIte,Option.getD_none]
    exact GeneralDictionaryDefaultExpression209.equivalent_refl _

 theorem recenter_holds {historical : Plan roles} (site : Site roles)
    (same : site.occurrence = historical.packet.site.occurrence)
    (collapsed : ∀ index, Equivalent
      (model (historical.input.occurrence.demand.arguments index).1).1
      (model (historical.input.occurrence.demand.arguments index).2).1)
    (center : site.Holds model)
    (old : GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
    GeneralNominalCenteredHeadMatStepPackets.Holds (recenter historical site same) model := by
  obtain ⟨head,input,binders,schema,equations,children⟩ := GeneralNominalCenteredHeadMatStepPackets.models_iff.mpr old
  apply GeneralNominalCenteredHeadMatStepPackets.models_iff.mp
  refine ⟨head,center,binders,?_,equations,children⟩
  apply GeneralDictionaryDefaultHeadTransport209.head_schema_transport
    (first := historical) (last := recenter historical site same) rfl rfl rfl
    (centers_equivalent historical.input site (historical.input_exact.trans same.symm) collapsed input center) _ schema
  intro name
  exact GeneralDictionaryDefaultExpression209.equivalent_refl _

 theorem recenter_class {historical : Plan roles} (site : Site roles)
    (same : site.occurrence = historical.packet.site.occurrence)
    (collapsed : ∀ index, Equivalent
      (model (historical.input.occurrence.demand.arguments index).1).1
      (model (historical.input.occurrence.demand.arguments index).2).1)
    (center : site.Holds model) (input : historical.input.Holds model) :
    ClassEffects core focus historical model ↔ ClassEffects core focus (recenter historical site same) model := by
  have bodies : ∀ target body, BodyHolds historical target model body ↔
      BodyHolds (recenter historical site same) target model body := by
    intro target body
    apply GeneralDictionaryDefaultBodyTransport209.body_transport (first := historical)
      (last := recenter historical site same) rfl rfl
    · intro name; exact GeneralDictionaryDefaultExpression209.equivalent_refl _
    · exact centers_equivalent historical.input site (historical.input_exact.trans same.symm) collapsed input center
  simp only [ClassEffects,bodies]
  rfl

 theorem certificate {state : GeneralNominalCenteredHeadMatStepJournal.State roles}
    {current historical : Plan roles}
    (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (collapsed : ∀ index, Equivalent (model (focus.demand.arguments index).1).1
      (model (focus.demand.arguments index).2).1)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet))
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus key current.packet.children current := by
  have same := current.input_exact.trans (frame.occurrence_eq.trans occurrence.symm)
  have data := GeneralDictionaryDefaultSemanticReplay209.recentered_data reachable frame member
    (GeneralDictionaryDefaultOutputBridge209.declaration_of_key checked reachable frame member keyEq) same report
  have old := valid.2.2.2.2.1 historical member
  have center := valid.2.2.2.1 current.input frame.center_recorded
  have oldCollapsed := (historical.input_exact.trans occurrence).symm ▸ collapsed
  have packet := recenter_holds current.input same oldCollapsed center old
  apply GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
  · exact GeneralDictionaryDefaultReinspection209.packet_reinspect data frame valid packet
  · exact GeneralDictionaryDefaultAvailability208.ready checked reachable frame
  · apply (GeneralDictionaryDefaultReinspection209.effects_same data).mpr
    exact (recenter_class current.input same oldCollapsed center
      (GeneralNominalCenteredHeadMatStepPackets.head_equations old).1).mp
      (occurrence ▸ GeneralDictionaryDefaultRecorded208.current_class reachable member valid)

 theorem nominal_certificate {state : GeneralNominalCenteredHeadMatStepJournal.State roles}
    {current historical : Plan roles}
    (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (collapsed : ∀ index, Equivalent (model (focus.demand.arguments index).1).1
      (model (focus.demand.arguments index).2).1)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (GeneralNominalCenteredHeadAllocEncoding.registry value)
      state.core model focus key current.packet.children current :=
  certificate checked reachable frame member keyEq occurrence collapsed
    (GeneralDictionaryDefaultSemanticReplay209.nominal_report checked reachable frame member keyEq occurrence refinement shape) valid

end Yulang.GeneralDictionaryDefaultCollapsedCenters209
