import Yulang.GeneralNominalBudgetContainer

/-! The actual P, Container, Wrap installation prefix. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalBudgetPrefix
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings GeneralNominalDownstreamSupport
open GeneralNominalDownstreamSiblingFixture
open GeneralDeclarationExamples (roles wrap wrap_checked containerChild)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
open GeneralNominalBudgetContainer (afterC cpkt)
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
local instance : NeZero afterP.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
local instance : NeZero afterC.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

noncomputable abbrev wpkt : Packet roles :=
  ⟨reg,afterC.current.context,GeneralNominalFeedbackSites.childSite pk kidW,wrap,wrap_checked,[(1,1)]⟩

theorem query : GeneralNominalInspection.queries afterC.current.context.state afterC.current.context.interpretation wrap =
    [.nominal 0 [.variables [0]]] := by
  change GeneralNominalInspection.queries src ctx.interpretation wrap = _
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]

theorem report : GeneralNominalRecursiveCandidates.report afterC.current.context wrap [(1,1)] =
    captured afterC.current.context.state 1 0 0 (2,2) :=
  report_exact afterC.current.context wrap 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl query

theorem bindings : wpkt.bindings = [(0,(2,2))] := by
  unfold Packet.bindings
  rw [report]
  rfl

theorem children : wpkt.children = [wrapChild] := by
  rw [←wrap_children]
  change GeneralNominalAllocation.children _ reg kidW wrap wrap_checked wpkt.bindings =
    GeneralNominalAllocation.children src reg kidW wrap wrap_checked wrapPacket.bindings
  rw [bindings,wrap_bindings]
  rfl

theorem located : GeneralNominalRecursiveCandidates.arguments afterC.current.context kidW = some [(1,1)] := by
  change GeneralCandidateBoundaryParts.locate src.base [kidW.demand.arguments ⟨0,by decide +kernel⟩] = _
  rw [child_inputs.2.1]
  have one : GeneralDictionaryBinderLocations.sourceSlot src.base 1 = some (1 : Fin 3) :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact src.base 1 1).mpr rfl
  simp [GeneralCandidateBoundaryParts.locate,one]
  rfl

theorem schema : GeneralNominalPacketSupport.namedSchema wpkt =
    ⟨[⟨1,.nominal (.source out) 0 0,.actual⟩,⟨1,.source wrapOutput,.actual⟩],
      [(.source out,.nominal 0 1)],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated reg afterC.current.context kidW wrap wrap_checked [(1,1)] = _
  unfold GeneralNominalRecursiveCandidates.generated
  rw [report]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  have catalogue : afterC.current.context.state.constructors = src.constructors := rfl
  have interpretation : afterC.current.context.interpretation = ctx.interpretation := rfl
  simp [catalogue,interpretation,GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,shared_output.2,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,GeneralNominalRecursiveInspection.bindings,captured,
    wrapOutput,GeneralNominalAllocation.allocation,src,GeneralNominalOutputGrowthModels.source]
  rfl

theorem outputs_eq (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalPacketSupport.Outputs wpkt model ↔ GeneralNominalPacketSupport.Outputs wrapPacket model := by
  unfold GeneralNominalPacketSupport.Outputs GeneralNominalPacketSupport.report
  rw [report,wrap_report,schema,cut_wrap_schema]
  unfold GeneralNominalPacketSupport.capture
  rw [bindings,wrap_bindings]
  simp only [GeneralNominalMaterialization.Models,captured,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq,forall_false,implies_true,and_true,true_and]
  rfl

theorem model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src assignment)
    (output : GeneralNominalPacketSupport.Outputs cutContainer assignment) : Models afterC.current assignment := by
  apply (GeneralNominalFeedbackSites.install_models afterP.current cpkt
    (GeneralNominalFeedbackSites.emitted cpkt) rfl assignment).mpr
  exact ⟨GeneralNominalBudgetContainer.source_model assignment valid,
    GeneralNominalBudgetContainer.branch assignment valid output⟩

theorem journal_model : Models afterC.current journalModel := by
  apply model journalModel cut_journal_models.1
  exact (GeneralNominalPacketSupport.packet_exact cutContainer journalModel).mp
    (cut_journal_models.2.1 cutContainer (by simp [cutJournal])) |>.2.2

theorem branch (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models afterC.current assignment)
    (outputs : GeneralNominalPacketSupport.Outputs wrapPacket assignment) : wpkt.Holds assignment := by
  have original := private_models afterC.current.context reg kidW wrap 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl query
    assignment valid.1
  exact ⟨original.1,original.2,(outputs_eq assignment).mpr outputs⟩

theorem journal_branch : wpkt.Holds journalModel := by
  apply branch journalModel journal_model
  exact (GeneralNominalPacketSupport.packet_exact wrapPacket journalModel).mp
    (cut_journal_models.2.1 wrapPacket (by simp [cutJournal])) |>.2.2

theorem source_members (identity : Nat) (member : identity ∈ GeneralNominalState.sources afterC.current.context.state) :
    identity ≤ 2 ∨ identity ∈ GeneralNominalAllocation.reserved src reg root.identity ∨
      identity ∈ GeneralNominalAllocation.reserved src reg kidC.identity := by
  change identity ∈ GeneralNominalState.sources
    (GeneralNominalRecursiveCandidates.privateState reg afterP.current.context kidC c [(1,1)]) at member
  unfold GeneralNominalRecursiveCandidates.privateState at member
  rw [GeneralNominalBudgetContainer.report] at member
  simp [GeneralNominalState.sources,GeneralNominalState.extend,GeneralNominalAllocation.propagate,
    GeneralNominalAllocation.cross,GeneralNominalAllocation.merges,GeneralNominalAllocation.occurrences,
    selfChecks,captured,GeneralNominalRecursiveInspection.bindings,
    GeneralNominalState.atomSources,GeneralNominalState.typeSources,GeneralNominalState.rowSources,
    GeneralNominalAllocation.Compatible,c,Declaration.inputNames,
    GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
    Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize] at member
  have old : identity ∈ GeneralNominalState.sources afterP.current.context.state →
      identity ≤ 2 ∨ identity ∈ GeneralNominalAllocation.reserved src reg root.identity ∨
        identity ∈ GeneralNominalAllocation.reserved src reg kidC.identity := by
    intro prior
    exact (GeneralNominalBudgetContainer.source_members identity prior).elim Or.inl (Or.inr ∘ Or.inl)
  rcases member with h | h | h | h | h | h | h | h
  · apply old
    simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]
    exact Or.inl (Or.inl (Or.inl h))
  · apply old
    simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]
    exact Or.inl (Or.inl (Or.inr h))
  · apply old
    simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]
    exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)
  · apply old
    apply List.mem_append_right
    exact List.mem_flatMap.mpr h
  · exact Or.inl (by change identity = 2 at h; omega)
  · exact Or.inl (by change identity = 1 at h; omega)
  · exact Or.inl (by change identity = 2 at h; omega)

theorem fresh (invocation : Nat) : GeneralNominalAllocation.Fresh afterC.current.context.state reg invocation := by
  intro key member collision
  rcases source_members _ collision with small | reserved | reserved
  · have large := GeneralNominalIdentities.source_above_seed src.seed key
    change 2 < GeneralNominalAllocation.source afterC.current.context.state reg invocation key at large
    omega
  · obtain ⟨old,owned,same⟩ := List.mem_map.mp reserved
    have equal : old = key := (GeneralNominalIdentities.source_identity src.seed old key).mp same
    subst old
    exact List.mem_append_left _ (List.mem_append_right _ owned)
  · obtain ⟨old,owned,same⟩ := List.mem_map.mp reserved
    have equal : old = key := (GeneralNominalIdentities.source_identity src.seed old key).mp same
    subst old
    exact List.mem_append_right _ owned

theorem linked : GeneralNominalState.Linked afterC.current.context.state kidW.demand := by
  constructor
  · intro index
    rw [child_inputs.2.1 index]
    have member : 1 ∈ GeneralNominalState.sources afterC.current.context.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨1,rfl⟩)))
    exact ⟨member,member⟩
  · intro output member
    rw [shared_output.2] at member
    have same := List.mem_singleton.mp member; subst output
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨GeneralNominalAllocation.origin root.identity p.id 2 2 0,by decide +kernel,rfl⟩

theorem wrap_only (candidate : Declaration) (visible : candidate ∈ reg.declarations)
    (role : candidate.role = kidW.demand.role) : candidate = wrap := by
  simp only [reg,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases role
  · cases role
  · rfl

theorem ready : ¬ GeneralNominalState.RootPending afterC.current.context.state kidW.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  rw [child_inputs.2.1 index]
  exact ⟨1,rfl,Or.inr ⟨GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _),rfl⟩⟩

theorem prepared : GeneralNominalRecursiveCandidates.Prepared reg afterC.current.context kidW wrap wrap_checked := by
  refine ⟨metadata,linked,fresh _,[(1,1)],located,?_,?_,journalModel,journal_branch⟩
  · rw [report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      rw [shared_output.2] at member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨GeneralDeclarationExamples.outDefinition,by simp [wrap],rfl⟩
    · change (GeneralNominalPacketSupport.namedSchema wpkt).unknown = false
      rw [schema]

theorem survivor : GeneralNominalRecursiveCandidates.Survivor reg afterC.current.context kidW wrap.id wpkt.children :=
  ⟨ready,wrap,by simp [reg],wrap_checked,rfl,rfl,[(1,1)],located,prepared,rfl⟩

theorem finite_model : Models afterC.current (GeneralNominalOutputGrowth.finiteModel 1) := by
  apply model _ ((GeneralNominalOutputGrowthModels.source_models 1 _).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1))
  apply cut_journal_facts (.outputs cutContainer []) (by simp [cutJournal])
  simp only [Fact.dependencies,List.mem_cons,List.not_mem_nil,or_false]
  intro same
  have equal := congrArg Occurrence.identity same
  exact (by decide +kernel : kidW.identity ≠ kidC.identity) equal

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle afterC.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic afterC.current (GeneralNominalOutputGrowth.finiteModel 1)
    finite_model (fun i => 2-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem raw_acyclic (slot : Fin src.base.slots) : ¬ GeneralNominalCycleK2.Cycle afterC.current.context.state slot := by
  let assignment := GeneralNominalOutputGrowth.finiteModel 1
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge afterC.current.context.state first last →
      2-last.val < 2-first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument assignment finite_model.1
      exact GeneralNominalOutputGrowthModels.observation_decreases assignment (fun i => 2-i) (fun _ => rfl) _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path afterC.current.context.state first last →
      2-last.val ≤ 2-first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 afterC.current kidW := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 reg afterC.current kidW := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem selected : GeneralNominalFeedbackK2.Local reg afterC.current kidW (.selected wrap.id wpkt.children) := by
  refine .selected ⟨ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,candidate,visible,certified,role,_,missing⟩ := pending
      have same := wrap_only candidate visible role
      subst candidate
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
  · intro key kids found
    have copy := found
    obtain ⟨_,candidate,visible,certified,identity,role,_⟩ := found
    have same := wrap_only candidate visible role
    subst candidate
    subst key
    exact ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional reg checked afterC.current.context kidW wrap.id kids wpkt.children copy survivor⟩

theorem sites : afterC.current.sites = afterP.current.sites := by
  change afterP.current.sites ++ cpkt.children.map (GeneralNominalFeedbackSites.childSite cpkt) = _
  rw [GeneralNominalBudgetContainer.children]
  simp

theorem packets : afterC.current.packets = [cpkt,pk] := rfl

theorem alias_identity (related : Alias afterC.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem site_role (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ afterC.current.sites)
    (role : other.occurrence.demand.role = kidW.demand.role) : other = wpkt.site := by
  rw [sites,GeneralNominalBudgetContainer.sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · cases role
  · cases role
  · rfl
  · cases role

theorem site_identity (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ afterC.current.sites)
    (identity : other.occurrence.identity = kidW.identity) : other = wpkt.site := by
  rw [sites,GeneralNominalBudgetContainer.sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : root.identity ≠ kidW.identity) identity)
  · exact False.elim ((by decide +kernel : kidC.identity ≠ kidW.identity) identity)
  · rfl
  · exact False.elim ((by decide +kernel : kidP.identity ≠ kidW.identity) identity)

theorem prior_unrelated (packet : Packet roles) (member : packet ∈ afterC.current.packets) :
    ¬ Alias afterC.current kidW.identity packet.site.occurrence.identity := by
  intro related
  rw [packets] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact (by decide +kernel : kidW.identity ≠ kidC.identity) (alias_identity related)
  · exact (by decide +kernel : kidW.identity ≠ root.identity) (alias_identity related)

theorem joint : GeneralNominalJointCandidates.Joint reg afterC.current kidW wrap.id := by
  have branchAt : GeneralNominalJointCandidates.BranchAt reg afterC.current kidW wrap.id journalModel :=
    ⟨wrap,by simp [reg],wrap_checked,rfl,rfl,prepared,[(1,1)],located,journal_branch⟩
  refine ⟨?_,journalModel,journal_model,branchAt,?_⟩
  · intro packet member related
    exact False.elim (prior_unrelated packet member related)
  · intro site related
    have equal := site_identity site related.1 (alias_identity related.2).symm
    subst site
    exact branchAt

theorem enabled : GeneralNominalFeedbackSteps.Installable reg afterC.current wpkt := by
  refine ⟨⟨rfl,rfl,?_,by simp [reg],rfl,located,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,joint⟩,selected,?_⟩
  · rw [sites,GeneralNominalBudgetContainer.sites]; simp [wpkt]
  · intro packet member related
    exact False.elim (prior_unrelated packet member related)
  · intro other member same
    have equal := site_role other member same.1.symm
    subst other
    exact .refl _
  · exact ⟨journalModel,journal_model,journal_branch⟩
  · intro other member same
    have equal := site_role other member same.1.symm
    subst other
    exact .refl _

theorem source_guard : GeneralNominalDownstreamSupport.PacketGuard afterC wpkt [] := by
  apply source_packet
  let descriptor := GeneralNominalOutputGrowthModels.descriptor 1 (1 : Fin src.base.slots) (Nat.le_refl _)
  have original : Head src 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := src) 1 descriptor rfl
  have current : Head afterC.current.context.state 1 (.nominal 0 1) (.nominal src.base 1 descriptor) :=
    Head.nominal (snapshot := afterC.current.context.state) (1 : Fin src.base.slots) descriptor rfl
  have ready : ReadyAt afterC [] 1 := source_ready afterC 1 _ _ _ original current []
  have reads : readsMany afterC.current.context.state
      (GeneralNominalInspection.queries afterC.current.context.state afterC.current.context.interpretation wrap) [(1,1)] = [1] := by
    rw [query]
    simp only [readsMany.eq_def,List.append_nil]
    rw [GeneralNominalSupport.reads.eq_def]
    change (1 : Fin src.base.slots) :: readsMany afterC.current.context.state [.variables [0]] [(2,2)] = [1]
    rw [readsMany.eq_def]
    simp only [GeneralNominalSupport.reads.eq_def,readsMany.eq_def,List.nil_append,List.append_nil]
    rfl
  have decisions : GeneralNominalSupport.DecisionGuard afterC reg kidW [] := by
    refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
    · intro index
      rw [child_inputs.2.1 index]
      exact ready
    · intro declaration visible sameRole bounds found slot member
      have same := wrap_only declaration visible sameRole
      subst declaration
      have equal := Option.some.inj (located.symm.trans found)
      subst bounds
      rw [reads] at member
      have equal := List.mem_singleton.mp member
      subst slot
      exact ready
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 wrap (by simp [reg]) rfl _ located⟩,decisions⟩

theorem edges : afterC.current.edges = [(root,kidC),(root,kidW),(root,kidP)] := by
  change ([] ++ pk.children.map (fun child => (pk.site.occurrence,child))) ++
    cpkt.children.map (fun child => (cpkt.site.occurrence,child)) = _
  rw [p_children,GeneralNominalBudgetContainer.children]
  rfl

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed afterC.current wpkt := by
  intro committed
  have child := committed.2 wrapChild (by rw [children]; simp)
  rw [edges] at child
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at child
  have impossible : kidW.identity ≠ root.identity := by decide +kernel
  rcases child with h | h | h
  all_goals exact impossible (congrArg Occurrence.identity h.1)

noncomputable def afterW : Tracked roles := GeneralNominalDownstreamSteps.install afterC wpkt []

theorem step : GeneralNominalDownstreamSteps.Step reg root afterC afterW :=
  ⟨kidW,GeneralNominalDownstreamSteps.generated_monotone GeneralNominalBudgetContainer.step children_generated.2.1,
    .install wpkt [] enabled novel source_guard⟩

theorem formed : GeneralNominalDownstreamSteps.SourceFormed reg root afterW :=
  .update GeneralNominalBudgetContainer.formed step

theorem actual_prefix : B4Target.Steps (GeneralNominalDownstreamSteps.Step reg root) start afterW :=
  .tail GeneralNominalBudgetContainer.actual_prefix step

theorem inputs_finite : GeneralNominalPacketSupport.Inputs wpkt (GeneralNominalOutputGrowth.finiteModel 1) := by
  let assignment := GeneralNominalOutputGrowth.finiteModel 1
  have original := private_models afterC.current.context reg kidW wrap 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl query assignment finite_model.1
  refine ⟨((GeneralNominalPacketSupport.private_exact wpkt assignment).mp original.1).2,original.2,?_⟩
  have empty : GeneralNominalPacketSupport.inputSchema wpkt = {} := by
    unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
    simp [GeneralNominalPacketSupport.inputSchema,GeneralNominalPacketSupport.inputRequests,
      GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil,List.mergeSort_singleton,GeneralDeclarationDemands.emitAll,
      GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,List.ofFn_succ,
      GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated]
  rw [empty]
  exact GeneralNominalMaterialization.empty_models ..

theorem cut (fact : Fact roles) (member : fact ∈ afterW.facts) (absent : kidW ∉ fact.dependencies) :
    fact.Holds (GeneralNominalOutputGrowth.finiteModel 1) := by
  rcases List.mem_append.mp member with added | prior
  · obtain ⟨support,_,member⟩ := List.mem_flatMap.mp added
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact inputs_finite
    · exact False.elim (absent (by exact List.mem_cons_self))
  · exact ((GeneralNominalDownstreamSteps.formed_exact GeneralNominalBudgetContainer.formed _).mp finite_model).2 fact prior

theorem cut_models (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models afterW.current assignment) :
    Models cutJournal.current assignment := by
  have source := (initial_models ctx root assignment).mp
    (GeneralNominalDownstreamSteps.steps_models actual_prefix assignment valid)
  have c_outputs := (GeneralNominalBudgetContainer.outputs_eq assignment).mp
    ((GeneralNominalPacketSupport.packet_exact cpkt assignment).mp
      (valid.2.1 cpkt (by change cpkt ∈ [wpkt,cpkt,pk]; simp))).2.2
  have w_outputs := (outputs_eq assignment).mp
    ((GeneralNominalPacketSupport.packet_exact wpkt assignment).mp
      (valid.2.1 wpkt (by change wpkt ∈ [wpkt,cpkt,pk]; simp))).2.2
  have container_query : GeneralNominalInspection.queries src ctx.interpretation c = [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
      GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source]
  have co := private_models ctx reg kidC c 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl container_query assignment source
  have wo := private_models ctx reg kidW wrap 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl query assignment source
  refine ⟨source,?_,?_⟩
  · intro packet member
    change packet ∈ [pk,cutContainer,wrapPacket] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact p_branch assignment source
    · exact ⟨co.1,co.2,c_outputs⟩
    · exact ⟨wo.1,wo.2,w_outputs⟩
  · intro site member
    obtain ⟨focus,_,rfl⟩ := List.mem_map.mp member
    exact point_holds focus assignment

theorem head : Available afterW 2 (.nominal 0 1) := by
  obtain ⟨snapshot,observation,recorded,entailed⟩ := cut_journal_head
  refine ⟨snapshot,observation,recorded,?_⟩
  intro assignment valid
  have actual := (GeneralNominalDownstreamSteps.formed_exact formed assignment).mpr
    ((pool_exact afterW assignment).mp valid)
  exact entailed assignment ((pool_exact cutJournal assignment).mpr
    ((cut_journal_exact assignment).mp (cut_models assignment actual)))

theorem after_alias_identity (related : Alias afterW.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem discharged (focus : Occurrence roles) (done : Discharged afterW.current focus) :
    focus.identity = kidC.identity := by
  induction done with
  | packet packet member done ih =>
    change packet ∈ [wpkt,cpkt,pk] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : wrapChild.identity ≠ kidC.identity)
        (ih wrapChild (by rw [children]; simp)))
    · rfl
    · exact False.elim ((by decide +kernel : kidW.identity ≠ kidC.identity)
        (ih kidW (by rw [p_children]; simp)))
  | alias first last _ _ related _ ih => exact (after_alias_identity related).symm.trans ih

theorem certificate : PrefixCertificate afterW := by
  have wrapOpen : ¬ Discharged afterW.current kidW := fun done =>
    (by decide +kernel : kidW.identity ≠ kidC.identity) (discharged kidW done)
  have childOpen : ¬ Discharged afterW.current wrapChild := fun done =>
    (by decide +kernel : wrapChild.identity ≠ kidC.identity) (discharged wrapChild done)
  refine ⟨rfl,wrapOpen,childOpen,?_,head,cut⟩
  apply Waiting.child (.root wrapOpen) _ childOpen
  apply List.mem_append_right
  rw [children]
  simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  rfl

theorem actual_wrap_not_grounded : ¬ Grounded reg afterW kidW := wrap_not_grounded certificate

theorem actual_downstream_head_blocked (support : List (Occurrence roles))
    (supported : Supported reg afterW support) : ¬ HeadSupported afterW support 2 (.nominal 0 1) :=
  downstream_head_blocked certificate support supported

/-- Observation replacement changes no provenance or discharge edges. This
corollary also covers a certified refresh exposing the journal head at 2. -/
noncomputable def observed (context : GeneralNominalCandidates.Context) : Tracked roles :=
  {afterW with current := regenerate afterW.current context}

theorem observed_alias_identity (context : GeneralNominalCandidates.Context)
    (related : Alias (observed context).current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem observed_discharged (context : GeneralNominalCandidates.Context) (focus : Occurrence roles)
    (done : Discharged (observed context).current focus) : focus.identity = kidC.identity := by
  induction done with
  | packet packet member done ih =>
    change packet ∈ [wpkt,cpkt,pk] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : wrapChild.identity ≠ kidC.identity)
        (ih wrapChild (by rw [children]; simp)))
    · rfl
    · exact False.elim ((by decide +kernel : kidW.identity ≠ kidC.identity)
        (ih kidW (by rw [p_children]; simp)))
  | alias first last _ _ related _ ih => exact (observed_alias_identity context related).symm.trans ih

theorem observed_certificate (context : GeneralNominalCandidates.Context) : PrefixCertificate (observed context) := by
  have wrapOpen : ¬ Discharged (observed context).current kidW := fun done =>
    (by decide +kernel : kidW.identity ≠ kidC.identity) (observed_discharged context kidW done)
  have childOpen : ¬ Discharged (observed context).current wrapChild := fun done =>
    (by decide +kernel : wrapChild.identity ≠ kidC.identity) (observed_discharged context wrapChild done)
  refine ⟨rfl,wrapOpen,childOpen,?_,head,cut⟩
  apply Waiting.child (.root wrapOpen) _ childOpen
  apply List.mem_append_right
  rw [children]
  simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  rfl

theorem observed_downstream_blocked (context : GeneralNominalCandidates.Context)
    (recorded : ∀ test observation, Head context.state 2 test observation → test = .nominal 0 1) :
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg (observed context) nextP support) ∧
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg (observed context) nextW support) :=
  first_P_and_W_blocked (observed_certificate context) recorded

end Yulang.GeneralNominalBudgetPrefix
