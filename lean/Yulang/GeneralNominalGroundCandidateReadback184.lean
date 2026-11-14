import Yulang.GeneralNominalGroundSiteCoherence184
import Yulang.GeneralNominalHeadTransport184

/-! Actual site registration discharges input-center coherence for candidate
head readback. A historical registered plan and same declaration/occurrence are
still explicit; no unrestricted candidate installation result is claimed. -/
namespace Yulang.GeneralNominalGroundCandidateReadback184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem registered_inputs
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, plan.input ∈ state.sites := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro historical member
      rcases List.mem_cons.mp member with rfl | old
      · exact List.mem_append_left _ guard.1
      · exact List.mem_append_left _ (ih historical old)

theorem ground_registered_input
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) : plan.input ∈ state.sites := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registered_inputs path plan member

theorem ground_input_equal (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence) :
    candidate.input = historical.input :=
  GeneralNominalGroundSiteCoherence184.ground_site_unique checked reachable candidate.input historical.input
    registered (ground_registered_input reachable historical member)
    (candidate.input_exact.trans (same.trans historical.input_exact.symm))

theorem candidate_actual (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (historical.binder entry.name)) := by
  have input := ground_input_equal checked reachable historical candidate member registered same
  apply GeneralNominalHeadTransport184.ground_candidate_actual reachable historical candidate member current declaration
    _ entry present actual model valid
  exact congrArg (fun site : Site roles => List.ofFn site.center) input

theorem candidate_nonpoint_overlap (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.plans)
    (registered : candidate.input ∈ state.sites)
    (same : candidate.packet.site.occurrence = historical.packet.site.occurrence)
    (current : candidate.packet.context = state.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (historicalNonpoint : ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture historical.packet).inputs entry.name).2)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  have centers := ground_input_equal checked reachable historical candidate member registered same
  apply GeneralNominalHeadTransport184.ground_candidate_nonpoint_overlap reachable historical candidate member
    current declaration (congrArg Occurrence.identity same)
    (congrArg (fun site : Site roles => List.ofFn site.center) centers)
    entry present actual input candidateNonpoint historicalNonpoint model valid

end Yulang.GeneralNominalGroundCandidateReadback184
