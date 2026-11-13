import Yulang.GeneralNominalProvenanceObserved
import Yulang.GeneralNominalProvenanceInputSupport
import Yulang.GeneralDictionaryFeedbackEvidence
import Yulang.GeneralNominalProvenanceExtractModel

/-! Candidate and transition obligations for the actual first emitted Extract
request, after both fresh endpoints have been observed. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenanceExtract
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource GeneralNominalProvenancePrefix
open GeneralNominalProvenanceObserved
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalSupport
open CommonNominalFullCarrier

noncomputable abbrev exPacket : Packet roles :=
  ⟨registry,observed.current.context,GeneralNominalFeedbackSites.childSite packet kidExtractA,
    extract,extract_checked,extractBounds⟩

private theorem current_sources (identity : Nat) (member : identity ∈ GeneralNominalState.sources current) :
    identity ≤ 7 ∨ identity ∈ GeneralNominalAllocation.reserved state registry root.identity := by
  change identity ∈ GeneralNominalState.sources (privateState registry context root p pBounds) at member
  unfold privateState at member
  rw [p_bindings,GeneralNominalProvenancePrefix.report_exact] at member
  simp [GeneralNominalState.sources,GeneralNominalState.extend,GeneralNominalAllocation.propagate,
    GeneralNominalAllocation.cross,GeneralNominalAllocation.merges,GeneralNominalAllocation.occurrences,
    Declaration.inputNames,p,normalizeArgs,normalize,variablesArgs,Pattern.variables,
    selfChecks,reportP,GeneralNominalState.atomSources,GeneralNominalState.typeSources,
    GeneralNominalState.rowSources] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first | exact Or.inr h | subst identity; exact Or.inl (by decide +kernel)

theorem fresh (invocation : Nat) : GeneralNominalAllocation.Fresh observed.current.context.state registry invocation := by
  intro key member collision
  have old := lower_certificate.support _ (upper_certificate.support _ collision)
  rcases current_sources _ old with small | reserved
  · have large := GeneralNominalIdentities.source_above_seed state.seed key
    change 7 < GeneralNominalAllocation.source observed.current.context.state registry invocation key at large
    omega
  · obtain ⟨previous,owned,equal⟩ := List.mem_map.mp reserved
    have same : previous = key := (GeneralNominalIdentities.source_identity state.seed previous key).mp equal
    subst previous
    exact List.mem_append_right _ owned

theorem output_request : kidExtractA.demand.outputs = [⟨1,output 3⟩] := rfl

theorem linked : GeneralNominalState.Linked observed.current.context.state kidExtractA.demand := by
  constructor
  · intro index
    rw [extract_arguments]
    exact ⟨GeneralNominalRefinements.sources upper_certificate.1 _
      (GeneralNominalRefinements.sources lower_certificate.refines _ lo_reserved),
      GeneralNominalRefinements.sources upper_certificate.refines _ upper_reserved⟩
  · intro outputRequest member
    rw [output_request] at member
    have same := List.mem_singleton.mp member
    subst outputRequest
    apply GeneralNominalRefinements.sources upper_certificate.1
    apply GeneralNominalRefinements.sources lower_certificate.1
    exact reserved_member 2 3 0 (by decide +kernel)

theorem schema_exact : generated registry observed.current.context kidExtractA extract extract_checked extractBounds =
    ⟨[⟨0,.source (output 3),.actual⟩],[],false⟩ := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests _ _ _ _ _ _ rfl]
  simp [GeneralNominalMaterialization.rootRequests,output_request,extract,
    GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,normalize]

theorem prepared (consistent : ∃ assignment, exPacket.Holds assignment) :
    Prepared registry observed.current.context kidExtractA extract extract_checked := by
  refine ⟨metadata,linked,fresh _,extractBounds,extract_located,extract_finished,?_,consistent⟩
  constructor
  · intro outputRequest member
    rw [output_request] at member
    have same := List.mem_singleton.mp member; subst outputRequest
    exact ⟨⟨601,1,.var 0⟩,by simp [extract],rfl⟩
  · rw [schema_exact]

theorem children : exPacket.children = [] := by
  simp [Packet.children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll,extract]

theorem survivor (consistent : ∃ assignment, exPacket.Holds assignment) :
    Survivor registry observed.current.context kidExtractA extract.id [] :=
  ⟨extract_ready,extract,by simp [registry],extract_checked,rfl,rfl,extractBounds,
    extract_located,prepared consistent,children.symm⟩

theorem witness_current : Models observed.current witness := by
  apply (observed_models witness).mpr
  apply (GeneralNominalFeedbackSites.install_models start.current packet _ rfl witness).mpr
  exact ⟨(GeneralNominalSaturationState.initial_models ..).mpr witness_source,branch⟩

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle observed.current identity :=
  witness_feedback_acyclic observed.current witness_current
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem no_raw (slot : Fin observed.current.context.state.base.slots) :
    ¬ GeneralNominalCycleK2.Cycle observed.current.context.state slot :=
  witness_raw_acyclic observed.current.context.state witness_current.1
    (by rintro _ _ ⟨kind,_,_,_⟩; exact Fin.elim0 kind) slot

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 observed.current kidExtractA := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry observed.current kidExtractA := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem extract_only (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = kidExtractA.demand.role) : declaration = extract := by
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases role

theorem selected (consistent : ∃ assignment, exPacket.Holds assignment) :
    GeneralNominalFeedbackK2.Local registry observed.current kidExtractA (.selected extract.id []) := by
  refine .selected ⟨extract_ready,no_root,no_candidate,?_⟩ ⟨survivor consistent,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,declaration,visible,certified,role,failed,missing⟩ := pending
      have same := extract_only declaration visible role
      subst declaration
      exact missing (prepared consistent)
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
  · intro key kids found
    have copy := found
    obtain ⟨_,declaration,visible,certified,identity,role,_⟩ := found
    have same := extract_only declaration visible role
    subst declaration
    subst key
    exact ⟨rfl,survivor_children_functional registry checked observed.current.context kidExtractA extract.id kids [] copy (survivor consistent)⟩


theorem reads_exact : readsMany observed.current.context.state
    (GeneralNominalInspection.queries observed.current.context.state observed.current.context.interpretation extract)
    extractBounds = [lowerSlot,upperSlot] := by
  rw [extract_query]
  simp only [extractBounds,readsMany.eq_1,reads.eq_5,lo_recorded,hi_recorded,currentDescriptor,
    GeneralNominalRecursiveInspection.typeArguments,slots_distinct,↓reduceIte,List.mapM_cons,List.mapM_nil]
  simp [readsMany.eq_1,readsMany.eq_2,reads.eq_1]

theorem source_guard : GeneralNominalSupportChoices.PacketGuard observed exPacket [] := by
  have roots : Roots observed [] kidExtractA := by
    intro index
    rw [extract_arguments]
    exact GeneralNominalProvenanceInputSupport.extract_lower_ready
  have inspection : Inspection observed [] extract extractBounds := by
    intro slot present
    rw [reads_exact] at present
    rcases List.mem_cons.mp present with same | rest
    · subst slot
      rw [lower_identity]
      exact GeneralNominalProvenanceInputSupport.extract_lower_ready
    · have same := List.mem_singleton.mp rest
      subst slot
      rw [upper_identity]
      exact GeneralNominalProvenanceInputSupport.extract_upper_ready
  refine ⟨⟨(by intro _ impossible; cases impossible),roots,inspection⟩,
    (by intro _ impossible; cases impossible),roots,?_⟩
  intro declaration visible role bounds found slot present
  have same := extract_only declaration visible role
  subst declaration
  have equal := Option.some.inj (extract_located.symm.trans found)
  subst bounds
  exact inspection slot present

theorem sites : observed.current.sites =
    [GeneralNominalDemandMerging.pointSite root,
      GeneralNominalFeedbackSites.childSite packet kidExtractA,
      GeneralNominalFeedbackSites.childSite packet kidW,
      GeneralNominalFeedbackSites.childSite packet kidExtractB,
      GeneralNominalFeedbackSites.childSite packet kidG,
      GeneralNominalFeedbackSites.childSite packet kidP] := by
  change [GeneralNominalDemandMerging.pointSite root] ++
    packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [GeneralNominalProvenancePrefix.children]
  rfl

theorem packets : observed.current.packets = [packet] := rfl

theorem alias_identity (related : Alias observed.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem site_role (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ observed.current.sites)
    (role : other.occurrence.demand.role = kidExtractA.demand.role) :
    other = exPacket.site ∨ other = GeneralNominalFeedbackSites.childSite packet kidExtractB := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · cases role
  · exact Or.inl rfl
  · cases role
  · exact Or.inr rfl
  · cases role
  · cases role

theorem root_different : kidExtractA.identity ≠ root.identity := by decide +kernel

theorem ea_w_different : kidExtractA.identity ≠ kidW.identity := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp equal
  have clause := congrArg (fun origin => origin.2.2.2.1) same
  cases clause

theorem ea_eb_different : kidExtractA.identity ≠ kidExtractB.identity := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp equal
  have clause := congrArg (fun origin => origin.2.2.2.1) same
  cases clause

theorem ea_g_different : kidExtractA.identity ≠ kidG.identity := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp equal
  have clause := congrArg (fun origin => origin.2.2.2.1) same
  cases clause

theorem ea_p_different : kidExtractA.identity ≠ kidP.identity := by
  intro equal
  have same := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp equal
  have clause := congrArg (fun origin => origin.2.2.2.1) same
  cases clause

theorem site_identity (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ observed.current.sites)
    (identity : other.occurrence.identity = kidExtractA.identity) : other = exPacket.site := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (root_different identity.symm)
  · rfl
  · exact False.elim (ea_w_different identity.symm)
  · exact False.elim (ea_eb_different identity.symm)
  · exact False.elim (ea_g_different identity.symm)
  · exact False.elim (ea_p_different identity.symm)

theorem prior_unrelated (prior : Packet roles) (member : prior ∈ observed.current.packets) :
    ¬ Alias observed.current kidExtractA.identity prior.site.occurrence.identity := by
  intro related
  rw [packets] at member
  have same := List.mem_singleton.mp member
  subst prior
  exact root_different (alias_identity related)

theorem joint (combined : ∃ assignment, Models observed.current assignment ∧ exPacket.Holds assignment) :
    GeneralNominalJointCandidates.Joint registry observed.current kidExtractA extract.id := by
  obtain ⟨assignment,valid,branch⟩ := combined
  have one : GeneralNominalJointCandidates.BranchAt registry observed.current kidExtractA extract.id assignment :=
    ⟨extract,by simp [registry],extract_checked,rfl,rfl,prepared ⟨assignment,branch⟩,
      extractBounds,extract_located,branch⟩
  refine ⟨?_,assignment,valid,one,?_⟩
  · intro prior member related
    exact False.elim (prior_unrelated prior member related)
  · intro other related
    have same := site_identity other related.1 (alias_identity related.2).symm
    subst other
    exact one


theorem extractB_arguments (index : Fin (roles kidExtractB.demand.role).arity) :
    kidExtractB.demand.arguments index = (argumentLo 12 0,argumentHi 12 0) := by
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp [kidExtractB,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.allocation,
    packet,extractB,zero,GeneralNominalDemandMerging.pointSite,normalize,argumentLo,argumentHi,allocated]

theorem same_inputs_entails (same : GeneralNominalFeedbackSites.SameInputs observed.current exPacket.site
    (GeneralNominalFeedbackSites.childSite packet kidExtractB))
    (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models observed.current assignment) :
    Equivalent (assignment 1).1 (assignment 4).1 := by
  let first := exPacket.site
  let last := GeneralNominalFeedbackSites.childSite packet kidExtractB
  let one : Fin (roles first.occurrence.demand.role).arity := ⟨0,by decide +kernel⟩
  let two : Fin (roles last.occurrence.demand.role).arity := ⟨0,by decide +kernel⟩
  have relation := same.2
  change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related (Models observed.current))
    [GeneralNominalFeedbackSites.recoverOrigin observed.current first one]
    [GeneralNominalFeedbackSites.recoverOrigin observed.current last two] at relation
  cases relation with
  | cons head tail =>
    obtain ⟨originA,originB,recordA,recordB,equal⟩ := head
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩,shared⟩ := equal assignment valid
    have firstMember : first ∈ observed.current.sites := by rw [sites]; simp [first,exPacket]
    have lastMember : last ∈ observed.current.sites := by rw [sites]; simp [last]
    have left := GeneralNominalFeedbackSites.recover_sound observed.current first assignment valid
      (valid.2.2 first firstMember)
    have right := GeneralNominalFeedbackSites.recover_sound observed.current last assignment valid
      (valid.2.2 last lastMember)
    have fitsA := left one originA (by
      change some (GeneralNominalFeedbackSites.recoverOrigin observed.current first one) = some (some originA)
      exact congrArg some recordA) |>.2 a ha
    have fitsB := right two originB (by
      change some (GeneralNominalFeedbackSites.recoverOrigin observed.current last two) = some (some originB)
      exact congrArg some recordB) |>.2 b hb
    change GeneralNominalCaptureMerges.Fits assignment (kidExtractA.demand.arguments one) a at fitsA
    change GeneralNominalCaptureMerges.Fits assignment (kidExtractB.demand.arguments two) b at fitsB
    erw [extract_arguments] at fitsA
    erw [extractB_arguments] at fitsB
    have initial := (observed_models assignment).mp valid
    have al := extractA_endpoints.1 assignment initial
    have au := extractA_endpoints.2 assignment initial
    have bl := extractB_endpoints.1 assignment initial
    have bu := extractB_endpoints.2 assignment initial
    have ab := shared a b ha hb
    exact ⟨subtype_trans al.2 (subtype_trans fitsA.1 (subtype_trans ab.1 (subtype_trans fitsB.2 bu.1))),
      subtype_trans bl.2 (subtype_trans fitsB.1 (subtype_trans ab.2 (subtype_trans fitsA.2 au.1)))⟩

theorem no_cross_merge : ¬ GeneralNominalFeedbackSites.SameInputs observed.current exPacket.site
    (GeneralNominalFeedbackSites.childSite packet kidExtractB) := by
  intro same
  let assignment := GeneralNominalProvenanceExtractModel.modelFor (.base .int) (.base .str) (.base .int)
  have equal := same_inputs_entails same assignment
    (GeneralNominalProvenanceExtractModel.observed_models (.base .int) (.base .str) (.base .int))
  have firstValue : (assignment 1).1 = nominal 0 [.inl (.base .int)] := by
    exact congrArg Prod.fst (GeneralNominalProvenanceExtractModel.source_small (.base .int) (.base .str) (.base .int) 1 (by decide +kernel))
  have lastValue : (assignment 4).1 = nominal 0 [.inl (.base .str)] := by
    exact congrArg Prod.fst (GeneralNominalProvenanceExtractModel.source_small (.base .int) (.base .str) (.base .int) 4 (by decide +kernel))
  rw [firstValue,lastValue] at equal
  have children := ((nominal_regular_invariant_exact ..).mp equal.1).2.2 0 (.inl (.base .int)) (.inl (.base .str)) rfl rfl
  have old : Common.Subtype (.base .int) (.base .str) :=
    (CommonNominalFullModelMap.subtype_exact _ _).mp children.1
  cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem merges_closed : GeneralNominalFeedbackSteps.MergesClosed observed.current exPacket.site := by
  intro other member same
  rcases site_role other member same.1.symm with equal | equal
  · subst other; exact .refl _
  · subst other; exact False.elim (no_cross_merge same)

theorem legacy_merges_closed : GeneralNominalCycleSteps.MergesClosed observed.current exPacket.site := by
  intro other member same
  exact merges_closed other member (GeneralDictionaryFeedbackEvidence.sameInputs_recovered observed.current exPacket.site other same)

theorem enabled : GeneralNominalFeedbackSteps.Installable registry observed.current exPacket := by
  have together := GeneralNominalProvenanceExtractModel.combined_models (.base .int) (.base .int) (.base .int)
  have consistency : ∃ assignment, exPacket.Holds assignment := ⟨_,together.2⟩
  have localSelected := selected consistency
  have packetSelected : GeneralNominalFeedbackK2.Local registry observed.current kidExtractA (.selected extract.id exPacket.children) := by
    rw [children]; exact localSelected
  refine ⟨⟨rfl,rfl,?_,by simp [registry],rfl,extract_located,prepared consistency,
    GeneralNominalFeedbackK2.selected_legacy packetSelected,?_,legacy_merges_closed,⟨_,together⟩,joint ⟨_,together⟩⟩,
    packetSelected,merges_closed⟩
  · rw [sites]; simp [exPacket]
  · intro prior member related
    exact False.elim (prior_unrelated prior member related)


theorem output_equation (assignment : GeneralNominalCommonBridge.Assignment) (branch : exPacket.Holds assignment) :
    Equivalent (assignment (output 3)).1 (assignment 2).1 := by
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound registry observed.current.context
    kidExtractA extract extract_checked extractBounds assignment branch).1
  have material := branch.2.2
  change GeneralNominalMaterialization.Models observed.current.context.state extract _
    (report observed.current.context extract extractBounds)
    (GeneralNominalRecursiveCandidates.generated registry observed.current.context kidExtractA extract extract_checked extractBounds)
    assignment at material
  rw [schema_exact,extract_report] at material
  have arg := nominal_argument_bounds observed.current.context.state assignment original lowerSlot currentDescriptor lo_recorded
    0 ((2 : Fin 10),(2 : Fin 10)) rfl
  obtain ⟨actual,seen⟩ := arg.1
  have fits := arg.2 actual seen
  rw [lower_identity] at seen
  have equal := material.2.2.2 ⟨0,.source (output 3),.actual⟩ (by simp)
    ⟨0,((2 : Fin 10),(2 : Fin 10)),some (.nominal (.source (argumentLo 10 0)) 0 0)⟩
    (by simp [extractReport]) rfl rfl _ rfl _ actual (.source (output 3)) seen
  have sourceTwo : observed.current.context.state.base.source (2 : Fin 10) = 2 := rfl
  change Subtype (assignment (observed.current.context.state.base.source (2 : Fin 10))).1 actual ∧
    Subtype actual (assignment (observed.current.context.state.base.source (2 : Fin 10))).1 at fits
  rw [sourceTwo] at fits
  exact ⟨subtype_trans equal.1 fits.2,subtype_trans fits.1 equal.2⟩

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed observed.current exPacket := by
  intro done
  have equal := output_equation witness (done.1 witness witness_current)
  change Equivalent (witness (allocated 2 3 0)).1 intValue at equal
  rw [witness_allocated] at equal
  have below := equal.2
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 1) ⟨rfl,by simp⟩

noncomputable def afterExtract : Tracked roles := GeneralNominalValueSteps.install observed exPacket []

theorem extract_step : GeneralNominalValueSteps.Step registry root observed afterExtract :=
  GeneralNominalValueSteps.source_install observed exPacket GeneralNominalProvenanceObserved.generated enabled novel source_guard

theorem extract_formed : GeneralNominalValueSteps.SourceFormed registry root afterExtract :=
  .update GeneralNominalProvenanceObserved.formed extract_step

theorem steps : B4Target.Steps (GeneralNominalValueSteps.Step registry root) start afterExtract :=
  .tail GeneralNominalProvenanceObserved.steps extract_step

theorem installed_output : GeneralNominalFeedbackK2.Equal afterExtract.current (output 3) 2 := by
  intro assignment valid
  exact output_equation assignment (valid.2.1 exPacket (by simp [afterExtract,GeneralNominalValueSteps.install,
    GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install]))

theorem discharged : Discharged afterExtract.current kidExtractA := by
  refine .packet exPacket ?_ ?_
  · simp [afterExtract,GeneralNominalValueSteps.install,GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install]
  · intro child member
    rw [children] at member
    cases member

end Yulang.GeneralNominalProvenanceExtract
