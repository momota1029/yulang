import Yulang.GeneralNominalCenteredPermutationCycles

set_option backward.isDefEq.respectTransparency false

/-! Applicability at paired observation contexts retains literal demands and
children. Journal conditions also retain the common branch-model witness. -/
namespace Yulang.GeneralNominalCenteredPermutationApplicability
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalJournalPermutation
open GeneralNominalCenteredPermutationContext (context)

variable {roles : Roles.RoleDecls} {one two : Context}

theorem prepared (same : ContextPair one two) (registry) (root : Occurrence roles) (decl)
    (checked : DeclarationChecked registry.constructors roles decl) :
    Prepared registry one root decl checked ↔ Prepared registry two root decl checked := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationContext.prepared one allocated reserved
    ⟨allocated,reserved,rfl,keys,names⟩ registry root decl checked).symm

theorem head_ready (same : ContextPair one two) (registry) (root : Occurrence roles) (decl) :
    HeadReady registry one root decl ↔ HeadReady registry two root decl := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationContext.head_ready one allocated reserved
    ⟨allocated,reserved,rfl,keys,names⟩ registry root decl).symm

theorem cycle_root (same : ContextPair one two) (root : Occurrence roles) :
    GeneralNominalCycleK2.RootK2 one.state root.demand ↔ GeneralNominalCycleK2.RootK2 two.state root.demand := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationCycles.root one.state allocated reserved
    ⟨allocated,reserved,rfl,keys,names⟩ root.demand).symm

theorem candidate (same : ContextPair one two) (registry) (root : Occurrence roles) :
    GeneralNominalCycleK2.CandidateK2 registry one root ↔ GeneralNominalCycleK2.CandidateK2 registry two root := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationCycles.candidate allocated reserved one
    ⟨allocated,reserved,rfl,keys,names⟩ registry root).symm

theorem inspection_pending (same : ContextPair one two) (registry) (root : Occurrence roles) :
    GeneralNominalCycleK2.InspectionPending registry one root ↔ GeneralNominalCycleK2.InspectionPending registry two root := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationCycles.inspection_pending allocated reserved one
    ⟨allocated,reserved,rfl,keys,names⟩ registry root).symm

theorem survivor (same : ContextPair one two) (registry) (root : Occurrence roles) (key children) :
    Survivor registry one root key children ↔ Survivor registry two root key children := by
  obtain ⟨allocated,reserved,rfl,keys,names⟩ := same.replace_form
  exact (GeneralNominalCenteredPermutationContext.survivor one allocated reserved
    ⟨allocated,reserved,rfl,keys,names⟩ registry root key children).symm

theorem cycle_local (same : ContextPair one two) (registry) (root : Occurrence roles) (frontier) :
    GeneralNominalCycleK2.Local registry one root frontier ↔ GeneralNominalCycleK2.Local registry two root frontier :=
  GeneralLocalPredicateCongruence.local_iff (first := GeneralNominalCycleK2.fields roles)
    (last := GeneralNominalCycleK2.fields roles)
    (GeneralNominalMetadataEquivalence.pending same.state root.demand) (cycle_root same root)
    (candidate same registry root) (inspection_pending same registry root) (survivor same registry root) frontier

variable {left right : GeneralNominalSaturationState.State roles}

theorem feedback_root (same : Related left right) (root : Occurrence roles) :
    GeneralNominalFeedbackK2.RootK2 left root ↔ GeneralNominalFeedbackK2.RootK2 right root := by
  simp only [GeneralNominalFeedbackK2.RootK2,cycle_root same.context root,
    GeneralNominalMetadataEquivalence.linked same.context.state,
    GeneralNominalMetadataEquivalence.pending same.context.state,same.recursAt]

theorem feedback_candidate (same : Related left right) (registry) (root : Occurrence roles) :
    GeneralNominalFeedbackK2.CandidateK2 registry left root ↔ GeneralNominalFeedbackK2.CandidateK2 registry right root := by
  rcases left with ⟨one,packets,sites,edges,aliases⟩
  rcases right with ⟨two,others,otherSites,otherEdges,otherAliases⟩
  obtain ⟨allocated,reserved,eq,keys,names⟩ := same.context.replace_form
  dsimp at eq
  subst two
  have recurs := same.recursAt
  have ready := head_ready (roles := roles) same.context
  have cycles := candidate same.context registry root
  have reports (decl bounds) :
      (report (⟨Metadata.replace one.state allocated reserved,one.interpretation⟩ : Context) decl bounds).inspected =
        (report one decl bounds).inspected :=
    congrArg GeneralNominalRecursiveInspection.Report.inspected
      (GeneralNominalCenteredPermutationContext.report one allocated reserved decl bounds)
  simp only [GeneralNominalFeedbackK2.CandidateK2,cycles,ready,reports,recurs]
  rfl

theorem feedback_local (same : Related left right) (registry) (root : Occurrence roles) (frontier) :
    GeneralNominalFeedbackK2.Local registry left root frontier ↔ GeneralNominalFeedbackK2.Local registry right root frontier :=
  GeneralLocalPredicateCongruence.local_iff (first := GeneralNominalFeedbackK2.fields roles)
    (last := GeneralNominalFeedbackK2.fields roles)
    (GeneralNominalMetadataEquivalence.pending same.context.state root.demand) (feedback_root same root)
    (feedback_candidate same registry root) (inspection_pending same.context registry root)
    (survivor same.context registry root) frontier

theorem branch_at (same : Related left right) (registry) (root : Occurrence roles) (key model) :
    GeneralNominalJointCandidates.BranchAt registry left root key model ↔
      GeneralNominalJointCandidates.BranchAt registry right root key model := by
  rcases left with ⟨one,packets,sites,edges,aliases⟩
  rcases right with ⟨two,others,otherSites,otherEdges,otherAliases⟩
  obtain ⟨allocated,reserved,eq,keys,names⟩ := same.context.replace_form
  dsimp at eq
  subst two
  have prep := prepared (roles := roles) same.context
  simp only [GeneralNominalJointCandidates.BranchAt,prep]
  change (∃ decl ∈ registry.declarations, ∃ checked, _ ∧ _ ∧ _ ∧ _) ↔
    (∃ decl ∈ registry.declarations, ∃ checked, _ ∧ _ ∧ _ ∧ _)
  have branches (decl checked bounds) :
      BranchModels registry (⟨Metadata.replace one.state allocated reserved,one.interpretation⟩ : Context)
        root decl checked bounds model ↔ BranchModels registry one root decl checked bounds model :=
    GeneralNominalCenteredPermutationContext.branch one allocated reserved registry root decl checked bounds model
  simp only [branches]
  rfl

theorem joint_forward (same : Related left right) (registry) (root : Occurrence roles) (key)
    (joint : GeneralNominalJointCandidates.Joint registry left root key) :
    GeneralNominalJointCandidates.Joint registry right root key := by
  refine ⟨?_,?_⟩
  · intro packet member alias
    obtain ⟨other,present,pair⟩ := same.packet_right member
    rw [← pair.identity]
    apply joint.1 other present
    apply (same.alias _ _).mpr
    rwa [pair.site]
  · obtain ⟨model,valid,branch,related⟩ := joint.2
    refine ⟨model,(same.models model).mp valid,(branch_at same registry root key model).mp branch,?_⟩
    intro site member
    exact (branch_at same registry site.occurrence key model).mp
      (related site ⟨same.sites.symm ▸ member.1,(same.alias _ _).mpr member.2⟩)

theorem joint (same : Related left right) (registry) (root : Occurrence roles) (key) :
    GeneralNominalJointCandidates.Joint registry left root key ↔ GeneralNominalJointCandidates.Joint registry right root key :=
  ⟨joint_forward same registry root key,joint_forward same.symm registry root key⟩

end Yulang.GeneralNominalCenteredPermutationApplicability
