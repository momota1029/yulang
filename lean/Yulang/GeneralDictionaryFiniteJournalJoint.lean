import Yulang.GeneralNominalStructuralSelectedGraph
import Yulang.GeneralDictionarySupportOrdinaryExecution

/-! Arbitrary finite journal Joint from actual site retention and ordinary
same-model replay. Unrelated packets remain unrestricted. -/
namespace Yulang.GeneralDictionaryFiniteJournalJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionaryRecursiveEvidence GeneralNominalJointCandidates

/-- Original sites are retained through every actual support update. -/
theorem step_sites {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (step : Step registry root before after) {site : GeneralNominalDemandMerging.Site roles}
    (member : site ∈ before.current.sites) : site ∈ after.current.sites := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative _ _ update =>
    cases update with
    | enqueue => exact List.mem_append_left _ member
    | refresh => exact member
    | equate => exact member
    | reobserve => exact member
  | install => exact List.mem_append_left _ member
  | merge => exact member

theorem steps_sites {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) {site : GeneralNominalDemandMerging.Site roles}
    (member : site ∈ before.current.sites) : site ∈ after.current.sites := by
  induction path with
  | refl => exact member
  | tail prior update ih => exact step_sites update ih

/-- No new existence or matching-site hypothesis is required for a real packet. -/
theorem packet_site (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state) (packet : Packet roles) (member : packet ∈ state.current.packets) :
    packet.site ∈ state.current.sites := by
  obtain ⟨before,support,_,_,enabled,_,_,path⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
  apply steps_sites path
  exact List.mem_append_left _ enabled.1.2.2.1

/-- Exact Related occurrence locality covers every alias-related stored packet,
because its original site is an actual current site. -/
theorem packet_locality (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (locality : ∀ site, Related state.current focus site → site.occurrence = focus)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (alias : Alias state.current focus.identity packet.site.occurrence.identity) : packet.site.occurrence = focus :=
  locality packet.site ⟨packet_site registry root state formed packet member,alias⟩

theorem ordinary_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (locality : ∀ site, Related state.current focus site → site.occurrence = focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
    packet member (growth packet member) same key children selected model valid
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  have branch := GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus key children
    survivor model replay.2.2
  refine ⟨?_,model,valid,branch,?_⟩
  · intro other present alias
    exact (GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed other present
      (growth other present) (packet_locality registry root focus state formed locality other present alias)
      key children selected model valid).1
  · intro site related
    rw [locality site related]
    exact branch

/-- Actual InitialSource and ordinary-only support execution supply source
formation and EVERY packet's growth, without per-edge or per-packet assumptions. -/
theorem initial_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (locality : ∀ site, Related state.current focus site → site.occurrence = focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key :=
  ordinary_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    packet member same key children selected locality model valid
end Yulang.GeneralDictionaryFiniteJournalJoint
