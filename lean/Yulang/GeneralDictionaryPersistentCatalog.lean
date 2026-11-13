import Yulang.GeneralDictionaryReachableRequestHistory

/-! Syntactic request coverage persists through actual transitions. No final
catalog inclusion or semantic request validity is assumed by the trace theorem. -/
namespace Yulang.GeneralDictionaryPersistentCatalog
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralDictionaryReachableRequestHistory
variable {roles : Roles.RoleDecls}

theorem safeCatalog_step {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (step : GeneralNominalValueSteps.Step registry root before after) :
    ∀ request ∈ safeCatalog before, request ∈ safeCatalog after := by
  obtain ⟨focus,reached,action⟩ := step
  cases action with
  | administrative focus state action =>
    intro request member
    simpa only [safeCatalog, administrative_packets action] using member
  | install packet support enabled novel guard =>
    intro request member
    rw [safeCatalog_install]
    exact List.mem_append_left _ member
  | merge first last support one two same novel guard =>
    intro request member
    exact member

theorem safeCatalog_trace {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after) :
    ∀ request ∈ safeCatalog before, request ∈ safeCatalog after := by
  induction path with
  | refl => exact fun _ member => member
  | tail _ step ih => exact fun request member => safeCatalog_step step request (ih request member)

theorem recorded_trace {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : packet ∈ before.current.packets)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []) :
    ∀ request ∈ emitted packet, request ∈ safeCatalog after :=
  fun request member => safeCatalog_trace path request (safe_member before packet recorded closed request member)
end Yulang.GeneralDictionaryPersistentCatalog
