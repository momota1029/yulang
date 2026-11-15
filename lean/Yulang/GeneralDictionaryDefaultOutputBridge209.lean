import Yulang.GeneralDictionaryDefaultPointTransport209

set_option backward.isDefEq.respectTransparency false

/-! Default-only current-class replay after reobservation. The restricted body
hypothesis is explicit; no current packet validity is inferred from it. -/
namespace Yulang.GeneralDictionaryDefaultOutputBridge209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}

 theorem stored_visible
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (present : historical ∈ state.core.plans) :
    historical.packet.declaration ∈ (registry value).declarations := by
  obtain ⟨effect,member,same⟩ := (GeneralDictionaryDefaultRecorded208.recorded reachable).2 historical present
  subst historical
  have seen := effect.frame.visible
  have configured : effect.registry = registry value := by
    obtain ⟨start,initial,path⟩ := reachable
    have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
    obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
    have old := GeneralDictionaryDefaultConfiguration209.stored
      (GeneralDictionaryDefaultTrace208.built_trace path) present
    exact effect.frame.registry_eq.symm.trans old.1
  exact configured ▸ seen

 theorem declaration_of_key
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key) :
    current.packet.declaration = historical.packet.declaration := by
  exact GeneralDictionaryEmissionPlans.declaration_key_unique (registry value)
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
    _ _ frame.visible (stored_visible reachable present) (frame.key_eq.trans keyEq.symm)

 theorem default_class
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (current.input.occurrence.demand.arguments index).1 =
      (current.input.occurrence.demand.arguments index).2)
    (defaults : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus,
      ∀ body, GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name = some body →
      ∃ role name term, body = .default role name term)
    (valid : Models state model) : ClassEffects state.core focus current model := by
  constructor
  · intro output member body found
    obtain ⟨role,name,term,rfl⟩ := defaults output member body found
    exact GeneralDictionaryDefaultPointTransport209.stored_default_output reachable frame present
      (declaration_of_key checked reachable frame present keyEq) occurrence point valid member found
  · exact occurrence ▸ (GeneralDictionaryDefaultRecorded208.current_class reachable present valid).2

/-- Given actual current packet semantics, the default-only replay fragment
builds a total certificate. Packet semantics are a separate remaining bridge. -/
 theorem default_certificate
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (current.input.occurrence.demand.arguments index).1 =
      (current.input.occurrence.demand.arguments index).2)
    (defaults : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus,
      ∀ body, GeneralDictionaryAssociatedProvenance.lookup roles current.packet.declaration output.name = some body →
      ∃ role name term, body = .default role name term)
    (valid : Models state model)
    (packet : GeneralNominalCenteredHeadMatStepPackets.Holds current model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key current.packet.children current :=
  GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl packet
    (GeneralDictionaryDefaultAvailability208.ready checked reachable frame)
    (default_class checked reachable frame present keyEq occurrence point defaults valid)

end Yulang.GeneralDictionaryDefaultOutputBridge209
