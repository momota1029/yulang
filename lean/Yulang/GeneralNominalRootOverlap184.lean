import Yulang.GeneralNominalOverlapIdentity184

/-! Root-only candidate head overlap readback. Generated demands are not
covered by root identity uniqueness. -/
namespace Yulang.GeneralNominalRootOverlap184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_root_identity
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.sites)
    (identity : site.occurrence.identity = root.identity) : site.occurrence = root := by
  rcases GeneralNominalSiteOrigin182.initial_site_origin path site registered with rfl | ⟨plan,member,emitted⟩
  · rfl
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
    have parent := ((GeneralNominalGroundSiteCoherence184.registered_producers path).2 plan member).1
    have child := GeneralNominalCenteredWhere.packet_child_above plan.packet _
      (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
        (plan.packet.checked.signature.2.2.2 clause.val clause.property))
    change (GeneralNominalFeedbackSites.clauseChild plan.packet clause.val _).identity = root.identity at identity
    omega

theorem ground_plan_root_identity
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans)
    (identity : plan.packet.site.occurrence.identity = root.identity) :
    plan.packet.site.occurrence = root := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [← plan.input_exact]
  exact trace_root_identity path plan.input
    (GeneralNominalGroundCandidateReadback184.registered_inputs path plan member)
    (congrArg Occurrence.identity plan.input_exact |>.trans identity)

theorem ground_plan_visible
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.declaration ∈ registry.declarations := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact ((GeneralNominalGroundSiteCoherence184.registered_producers path).2 plan member).2

theorem candidate_root_overlap (checked : Checked registry)
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralNominalModeLedger181.fullSources state)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  have allocated := GeneralNominalBinderIdentity181.binder_fresh candidate entry.name input nonpoint
  rw [current] at allocated
  rw [allocated] at overlap
  obtain ⟨_,historical,member,_,_,_,_,_,_,identity,decl,_,oldNonpoint,_⟩ :=
    GeneralNominalOverlapIdentity184.ground_overlap_producer reachable overlap
  have historicalRoot := ground_plan_root_identity reachable historical member
    (identity.trans (congrArg Occurrence.identity atRoot))
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    candidate.packet.declaration historical.packet.declaration visible
    (ground_plan_visible reachable historical member) decl.symm
  exact GeneralNominalGroundCandidateReadback184.candidate_nonpoint_overlap checked reachable
    historical candidate member registered (atRoot.trans historicalRoot.symm) current declaration
    entry present actual input nonpoint oldNonpoint model valid

end Yulang.GeneralNominalRootOverlap184
