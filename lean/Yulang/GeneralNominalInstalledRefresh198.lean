import Yulang.GeneralNominalMixedTree198

/-! A genuine initial installation followed by a descriptor-changing refresh.
The installed packet is recovered from the real journal, not supplied as a
final Instance. Operational enabling and old nominal syntax remain explicit. -/
namespace Yulang.GeneralNominalInstalledRefresh198
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMixedJournal197 (MixedStep)
open GeneralNominalViewTransport196 (View)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry}
variable {context : GeneralNominalCandidates.Context} {root : Occurrence roles}
variable {plan : Plan roles} {support : List (Occurrence roles)}

abbrev start (context : GeneralNominalCandidates.Context) (root : Occurrence roles) := initial context root

variable (enabled : Installable registry (start context root) plan support)
variable (generated : GeneralNominalSaturationState.Generated (start context root).core.erased.current root plan.packet.site.occurrence)
variable (novel : ¬ GeneralNominalFeedbackSteps.Committed (start context root).core.erased.current plan.packet)

noncomputable abbrev middle := install (start context root) plan support enabled

variable {next : View (middle enabled).core.erased.current.context.state}
noncomputable abbrev refreshed := refresh (middle enabled)
  (GeneralNominalViewTransport196.context (middle enabled).core.erased.current.context next)

variable (certificate : GeneralNominalCenteredSteps.Refresh (middle enabled).core
  (GeneralNominalViewTransport196.context (middle enabled).core.erased.current.context next))
variable (shape : GeneralNominalSyntaxRefresh197.RegistrySyntax registry (middle enabled).core.erased.current.context)
variable (source : Nat)
variable (present : source ∈ GeneralNominalState.sources (middle enabled).core.erased.current.context.state)
variable (unknown : ¬ GeneralNominalState.Known (middle enabled).core.erased.current.context.state source)
variable (known : GeneralNominalState.Known (GeneralNominalViewTransport196.replace
  (middle enabled).core.erased.current.context.state next) source)

include generated novel in
theorem installation : MixedStep registry root (start context root) (middle enabled) := by
  have ordinary := GeneralNominalOrdinaryEvidence191.install_step enabled generated novel
  exact ⟨ordinary.1,Or.inl ordinary.2⟩

include certificate shape source present unknown known in
theorem refresh_step : MixedStep registry root (middle enabled) (refreshed enabled (next := next)) :=
  ⟨⟨root,.root,.refresh root _ certificate source present unknown known⟩,
    Or.inr ⟨next,rfl,certificate.refines,shape⟩⟩


include generated novel certificate shape source present unknown known in
/-- Both edges are actual WF transitions, not merely a semantic context relation. -/
theorem path : B4Target.Steps (MixedStep registry root) (start context root)
    (refreshed enabled (next := next)) :=
  .tail (.tail .refl (installation enabled generated novel))
    (refresh_step enabled certificate shape source present unknown known)

theorem packet_recorded : plan.packet ∈ (refreshed enabled (next := next)).core.erased.current.packets :=
  List.mem_cons_self ..

include generated novel certificate shape source present unknown known in
theorem packet_instance (model : Assignment) (valid : Models (refreshed enabled (next := next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry
      (refreshed enabled (next := next)).core.erased.current.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children :=
  GeneralNominalMixedJournal197.packet_instance
    (path enabled generated novel certificate shape source present unknown known)
    plan.packet (packet_recorded enabled) model valid


include generated novel certificate shape source present unknown known in
/-- Node soundness after the actual two-edge history requires only the child
Evidence in the final assignment, not a stale or final parent Instance. -/
theorem evidence_node (model : Assignment) (valid : Models (refreshed enabled (next := next)) model)
    (payloads : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂
      ((boundary roles).Evidence registry (refreshed enabled (next := next)) model) plan.packet.children payloads) :
    (boundary roles).Evidence registry (refreshed enabled (next := next)) model plan.packet.site.occurrence
      (.node plan.packet.declaration.id payloads) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry _ model _ _ _ payloads
    (packet_instance enabled generated novel certificate shape source present unknown known model valid) children


include generated novel certificate shape source present unknown known in
/-- A leaf packet needs no child-side semantic premise at all. -/
theorem leaf_evidence (empty : plan.packet.children = [])
    (model : Assignment) (valid : Models (refreshed enabled (next := next)) model) :
    (boundary roles).Evidence registry (refreshed enabled (next := next)) model plan.packet.site.occurrence
      (.node plan.packet.declaration.id []) := by
  apply evidence_node enabled generated novel certificate shape source present unknown known model valid []
  rw [empty]
  exact .nil

include certificate in
theorem models_iff (model : Assignment) :
    Models (refreshed enabled (next := next)) model ↔ Models (middle enabled) model :=
  refresh_models certificate model
end Yulang.GeneralNominalInstalledRefresh198
