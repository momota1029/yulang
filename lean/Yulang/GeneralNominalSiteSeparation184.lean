import Yulang.GeneralNominalSiteSupport184

/-! Raw shared child sites cannot introduce high-namespace names when their
historical context and parent site exclude that name. -/
namespace Yulang.GeneralNominalSiteSeparation184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)
open GeneralNominalSiteSupport184
open GeneralNominalCenteredModelExtension (originSource)

variable {roles : Roles.RoleDecls}

theorem clause_endpoints (packet : GeneralNominalSaturationState.Packet roles)
    (clause : Clause) (signature : clause.Signature roles)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (index : Fin (roles clause.role).arity) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalFeedbackSites.clauseChild packet clause signature).demand.arguments index).1 ∧
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalFeedbackSites.clauseChild packet clause signature).demand.arguments index).2 := by
  change _ ≠ (GeneralDeclarationDemands.inputInterval _ _ _).1 ∧
    _ ≠ (GeneralDeclarationDemands.inputInterval _ _ _).2
  unfold GeneralDeclarationDemands.inputInterval
  split
  · exact GeneralNominalRawSupport183.capture_inputs_separate packet high outside _
  all_goals exact ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3),
    GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4)⟩

theorem child_endpoints (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    ∀ index, fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (child.demand.arguments index).1 ∧
      fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (child.demand.arguments index).2 := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children at member
  obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
  have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mpr present
  unfold GeneralDeclarationDemands.emitAll at old
  obtain ⟨clause,_,equal⟩ := List.mem_map.mp old
  cases equal
  exact clause_endpoints packet clause.val _ high outside

theorem child_separate (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (high : 7 ≤ purpose)
    (context : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (parent : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources packet.site) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources (GeneralNominalSharedEmission.childSite packet child) := by
  intro present
  let names := inheritedSources packet ++
    (List.ofFn fun index => [(child.demand.arguments index).1,(child.demand.arguments index).2]).flatten
  have supported : rawSiteSources (GeneralNominalSharedEmission.childSite packet child) ⊆ names := by
    apply child_sources packet child (fun _ h => List.mem_append_left _ h)
    intro index
    constructor <;> apply List.mem_append_right _ <;> apply List.mem_flatten.mpr <;>
      refine ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,?_⟩ <;> simp
  rcases List.mem_append.mp (supported present) with old | endpoint
  · rcases List.mem_append.mp old with ctx | site
    · exact context ctx
    · exact parent site
  · obtain ⟨pair,pairMember,inside⟩ := List.mem_flatten.mp endpoint
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp pairMember
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with equal | equal
    · exact (child_endpoints packet child member high context index).1 equal
    · exact (child_endpoints packet child member high context index).2 equal
end Yulang.GeneralNominalSiteSeparation184
