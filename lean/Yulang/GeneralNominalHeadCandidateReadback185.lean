import Yulang.GeneralNominalHeadSiteCoherence185
import Yulang.GeneralNominalHeadReadback185

/-! Actual site registration discharges input-center coherence for candidate
head readback. A historical registered plan and same declaration/occurrence are
still explicit; no unrestricted candidate installation result is claimed. -/
namespace Yulang.GeneralNominalHeadCandidateReadback185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem registered_inputs
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.input ∈ state.core.sites := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro historical member
      rcases List.mem_cons.mp member with rfl | old
      · exact List.mem_append_left _ enabled.frame.center_recorded
      · exact List.mem_append_left _ (ih historical old)

theorem wf_registered_input
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) : plan.input ∈ state.core.sites := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact registered_inputs path plan member

theorem wf_input_equal (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence) :
    candidate.input = historical.input :=
  GeneralNominalHeadSiteCoherence185.wf_site_unique checked reachable candidate.input historical.input
    registered (wf_registered_input reachable historical member)
    (candidate.input_exact.trans (same.trans historical.input_exact.symm))

theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name)) := by
  have input := wf_input_equal checked reachable historical candidate member registered same
  apply GeneralNominalHeadReadback185.wf_candidate_actual reachable historical candidate member current declaration
    _ entry present actual model valid
  exact congrArg (fun site : Site roles => List.ofFn site.center) input

theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  have centers := wf_input_equal checked reachable historical candidate member registered same
  apply GeneralNominalHeadReadback185.wf_candidate_nonpoint_overlap reachable historical candidate member
    current declaration (congrArg Occurrence.identity same)
    (congrArg (fun site : Site roles => List.ofFn site.center) centers)
    entry present actual input candidateNonpoint historicalNonpoint model valid

end Yulang.GeneralNominalHeadCandidateReadback185
