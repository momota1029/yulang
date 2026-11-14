import Yulang.GeneralNominalHeadBinderIdentity185
import Yulang.GeneralNominalHeadFullProducer185

/-! Root-only candidate head overlap readback. Generated demands are not
covered by root identity uniqueness. -/
namespace Yulang.GeneralNominalHeadRootOverlap185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_root_identity
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (identity : site.occurrence.identity = root.identity) : site.occurrence = root := by
  rcases GeneralNominalHeadSiteOrigin185.initial_site_origin path site registered with rfl | ⟨plan,member,emitted⟩
  · rfl
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
    have parent := ((GeneralNominalHeadSiteCoherence185.registered_producers path).2 plan member).1
    have child := GeneralNominalCenteredWhere.packet_child_above plan.packet _
      (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
        (plan.packet.checked.signature.2.2.2 clause.val clause.property))
    change (GeneralNominalFeedbackSites.clauseChild plan.packet clause.val _).identity = root.identity at identity
    omega

theorem wf_plan_root_identity
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans)
    (identity : plan.packet.site.occurrence.identity = root.identity) :
    plan.packet.site.occurrence = root := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  rw [← plan.input_exact]
  exact trace_root_identity path plan.input
    (GeneralNominalHeadCandidateReadback185.registered_inputs path plan member)
    (congrArg Occurrence.identity plan.input_exact |>.trans identity)

theorem wf_plan_visible
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.core.plans) :
    plan.packet.declaration ∈ registry.declarations := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact ((GeneralNominalHeadSiteCoherence185.registered_producers path).2 plan member).2

theorem candidate_root_overlap (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (registered : candidate.input ∈ state.core.sites)
    (atRoot : candidate.packet.site.occurrence = root)
    (current : candidate.packet.context = state.core.erased.current.context)
    (visible : candidate.packet.declaration ∈ registry.declarations)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralNominalHeadLedgerFrame182.fullSources state)
    (model : Assignment) (valid : Models state model) :
    Same model entry.origin (.source (candidate.binder entry.name)) := by
  have allocated := GeneralNominalBinderIdentity181.binder_fresh candidate entry.name input nonpoint
  rw [current] at allocated
  rw [allocated] at overlap
  obtain ⟨historical,member,name,equal⟩ :=
    GeneralNominalHeadFullProducer185.wf_full_producer reachable overlap
  obtain ⟨nameEq,_,identity,decl,_,oldNonpoint⟩ :=
    GeneralNominalHeadBinderIdentity185.registered_binder_identity reachable historical member name equal
  subst name
  have historicalRoot := wf_plan_root_identity reachable historical member
    (identity.trans (congrArg Occurrence.identity atRoot))
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    candidate.packet.declaration historical.packet.declaration visible
    (wf_plan_visible reachable historical member) decl.symm
  exact GeneralNominalHeadCandidateReadback185.candidate_nonpoint_overlap checked reachable
    historical candidate member registered (atRoot.trans historicalRoot.symm) current declaration
    entry present actual input nonpoint oldNonpoint model valid

end Yulang.GeneralNominalHeadRootOverlap185
