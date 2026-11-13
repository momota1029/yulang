import Yulang.GeneralNominalDownstreamSiblingFixture
import Yulang.GeneralNominalDownstreamExamples

/-! Actual Container installation after the source-supported P packet. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalBudgetContainer
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSiblingFixture
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
local instance : NeZero afterP.current.context.state.base.slots := ⟨by change 1+2 ≠ 0; omega⟩

noncomputable abbrev cpkt := containerPacket

theorem report : GeneralNominalRecursiveCandidates.report afterP.current.context c [(1,1)] =
    captured afterP.current.context.state 1 0 0 (2,2) := by
  apply report_exact afterP.current.context c 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 (2,2) rfl
  change GeneralNominalInspection.queries src ctx.interpretation c = _
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source,GeneralNominalOutputGrowthModels.descriptor]

theorem bindings : cpkt.bindings = [(0,(2,2))] := by
  unfold Packet.bindings
  rw [report]
  rfl

theorem children : cpkt.children = [] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    c,GeneralDeclarationDemands.emitAll]

theorem located : GeneralNominalRecursiveCandidates.arguments afterP.current.context kidC = some [(1,1)] := by
  change GeneralCandidateBoundaryParts.locate src.base [kidC.demand.arguments ⟨0,by decide +kernel⟩] = _
  rw [child_inputs.1]
  have one : GeneralDictionaryBinderLocations.sourceSlot src.base 1 = some (1 : Fin 3) :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact src.base 1 1).mpr rfl
  simp [GeneralCandidateBoundaryParts.locate,one]
  rfl

theorem schema : GeneralNominalPacketSupport.namedSchema cpkt =
    ⟨[⟨0,.source out,.actual⟩],[],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated reg afterP.current.context kidC c c_checked [(1,1)] = _
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests
    GeneralNominalMaterialization.rootRequests
  rw [shared_output.1]
  unfold GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,c]

theorem outputs_eq (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalPacketSupport.Outputs cpkt model ↔ GeneralNominalPacketSupport.Outputs cutContainer model := by
  unfold GeneralNominalPacketSupport.Outputs GeneralNominalPacketSupport.report
  rw [report,cut_container_report,schema,cut_container_schema]
  unfold GeneralNominalPacketSupport.capture
  rw [bindings,cut_container_bindings]
  simp only [GeneralNominalMaterialization.Models,captured,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq,forall_false,implies_true,and_true,true_and]
  rfl

theorem source_model (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) : Models afterP.current model := by
  apply (GeneralNominalFeedbackSites.install_models start.current pk (GeneralNominalFeedbackSites.emitted pk) rfl model).mpr
  exact ⟨(initial_models ctx root model).mpr valid,p_branch model valid⟩

theorem branch (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model)
    (outputs : GeneralNominalPacketSupport.Outputs cutContainer model) : cpkt.Holds model := by
  have original := private_models afterP.current.context reg kidC c 1
    (GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _)) rfl 0 rfl (2,2) rfl
    (by
      change GeneralNominalInspection.queries src ctx.interpretation c = _
      simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
        GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
        GeneralNominalExamples.interpretation,src,GeneralNominalOutputGrowthModels.source,GeneralNominalOutputGrowthModels.descriptor])
    model (source_model model valid).1
  exact ⟨original.1,original.2,(outputs_eq model).mpr outputs⟩

theorem journal_branch : cpkt.Holds journalModel := by
  apply branch journalModel cut_journal_models.1
  exact (GeneralNominalPacketSupport.packet_exact cutContainer journalModel).mp
    (cut_journal_models.2.1 cutContainer (by simp [cutJournal])) |>.2.2

theorem source_members (identity : Nat) (member : identity ∈ GeneralNominalState.sources afterP.current.context.state) :
    identity ≤ 2 ∨ identity ∈ GeneralNominalAllocation.reserved src reg root.identity := by
  change identity ∈ GeneralNominalState.sources (GeneralNominalRecursiveCandidates.privateState reg ctx root p bs) at member
  unfold GeneralNominalRecursiveCandidates.privateState at member
  rw [p_report] at member
  simp [GeneralNominalState.sources,GeneralNominalState.extend,GeneralNominalAllocation.propagate,
    GeneralNominalAllocation.cross,GeneralNominalAllocation.merges,GeneralNominalAllocation.occurrences,
    selfChecks,bindings,captured,GeneralNominalRecursiveInspection.bindings,
    GeneralNominalState.atomSources,
    GeneralNominalState.typeSources,GeneralNominalState.rowSources,
    GeneralNominalOutputGrowthModels.source,GeneralNominalOutputGrowthModels.base,src,
    List.ofFn_succ,GeneralNominalAllocation.Compatible,p,Declaration.inputNames,
    GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
    Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize] at member
  change identity = 0 ∨ identity = 1 ∨ identity = 2 ∨ identity = 0 ∨ identity = 1 ∨ identity = 2 ∨
    identity ∈ GeneralNominalAllocation.reserved src reg root.identity ∨ identity = 1 ∨ identity = 0 ∨ identity = 1 at member
  rcases member with h | h | h | h | h | h | h | h | h | h
  all_goals first | exact Or.inr h | exact Or.inl (by omega)


theorem fresh (invocation : Nat) : GeneralNominalAllocation.Fresh afterP.current.context.state reg invocation := by
  intro key member collision
  rcases source_members _ collision with small | reserved
  · have large := GeneralNominalIdentities.source_above_seed src.seed key
    change 2 < GeneralNominalAllocation.source afterP.current.context.state reg invocation key at large
    omega
  · obtain ⟨old,owned,same⟩ := List.mem_map.mp reserved
    have equal : old = key := (GeneralNominalIdentities.source_identity src.seed old key).mp same
    subst old
    exact List.mem_append_right _ owned

theorem source_slot_member (slot : Fin src.base.slots) :
    src.base.source slot ∈ GeneralNominalState.sources afterP.current.context.state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem output_member : out ∈ GeneralNominalState.sources afterP.current.context.state := by
  have reserved : out ∈ GeneralNominalAllocation.reserved src reg root.identity := by
    exact List.mem_map.mpr ⟨GeneralNominalAllocation.origin root.identity p.id 2 2 0,by decide +kernel,rfl⟩
  apply List.mem_append_left
  apply List.mem_append_right
  change out ∈ [] ++ GeneralNominalAllocation.reserved src reg root.identity ++ []
  simpa using reserved

theorem linked : GeneralNominalState.Linked afterP.current.context.state kidC.demand := by
  constructor
  · intro index
    rw [child_inputs.1 index]
    exact ⟨source_slot_member 1,source_slot_member 1⟩
  · intro output member
    rw [shared_output.1] at member
    have same := List.mem_singleton.mp member
    subst output
    exact output_member

theorem c_only (candidate : Declaration) (visible : candidate ∈ reg.declarations)
    (role : candidate.role = kidC.demand.role) : candidate = c := by
  simp only [reg,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases role
  · rfl
  · cases role

theorem ready : ¬ GeneralNominalState.RootPending afterP.current.context.state kidC.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  rw [child_inputs.1 index]
  exact ⟨1,rfl,Or.inr ⟨GeneralNominalOutputGrowthModels.descriptor 1 1 (Nat.le_refl _),rfl⟩⟩

theorem prepared : GeneralNominalRecursiveCandidates.Prepared reg afterP.current.context kidC c c_checked := by
  refine ⟨metadata,linked,fresh _,[(1,1)],located,?_,?_,journalModel,journal_branch⟩
  · rw [report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      rw [shared_output.1] at member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨⟨105,1,.var 0⟩,by simp [c],rfl⟩
    · change (GeneralNominalPacketSupport.namedSchema cpkt).unknown = false
      rw [schema]

theorem survivor : GeneralNominalRecursiveCandidates.Survivor reg afterP.current.context kidC c.id cpkt.children :=
  ⟨ready,c,by simp [reg],c_checked,rfl,rfl,[(1,1)],located,prepared,rfl⟩

theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle afterP.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic afterP.current (GeneralNominalOutputGrowth.finiteModel 1)
    (source_model _ ((GeneralNominalOutputGrowthModels.source_models 1 _).mpr (GeneralNominalOutputGrowth.finite_prefix_models 1)))
    (fun i => 2-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem raw_acyclic (slot : Fin src.base.slots) : ¬ GeneralNominalCycleK2.Cycle afterP.current.context.state slot := by
  let model := GeneralNominalOutputGrowth.finiteModel 1
  have valid := (source_model model ((GeneralNominalOutputGrowthModels.source_models 1 model).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1))).1
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge afterP.current.context.state first last →
      2-last.val < 2-first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model valid
      exact GeneralNominalOutputGrowthModels.observation_decreases model (fun i => 2-i) (fun _ => rfl) _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path afterP.current.context.state first last →
      2-last.val ≤ 2-first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 afterP.current kidC := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 reg afterP.current kidC := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem selected : GeneralNominalFeedbackK2.Local reg afterP.current kidC (.selected c.id cpkt.children) := by
  refine .selected ⟨ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,candidate,visible,certified,role,_,missing⟩ := pending
      have same := c_only candidate visible role
      subst candidate
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle; exact Fin.elim0 kind
  · intro key kids found
    have copy := found
    obtain ⟨_,candidate,visible,certified,identity,role,_⟩ := found
    have same := c_only candidate visible role
    subst candidate
    subst key
    exact ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional reg checked afterP.current.context kidC c.id kids cpkt.children copy survivor⟩


theorem sites : afterP.current.sites = [GeneralNominalDemandMerging.pointSite root,
    GeneralNominalFeedbackSites.childSite pk kidC,GeneralNominalFeedbackSites.childSite pk kidW,
    GeneralNominalFeedbackSites.childSite pk kidP] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ pk.children.map (GeneralNominalFeedbackSites.childSite pk) = _
  rw [p_children]
  rfl

theorem alias_identity (related : Alias afterP.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem site_role (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ afterP.current.sites)
    (role : other.occurrence.demand.role = kidC.demand.role) : other = cpkt.site := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · cases role
  · rfl
  · cases role
  · cases role

theorem site_identity (other : GeneralNominalDemandMerging.Site roles) (member : other ∈ afterP.current.sites)
    (identity : other.occurrence.identity = kidC.identity) : other = cpkt.site := by
  rw [sites] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : root.identity ≠ kidC.identity) identity)
  · rfl
  · exact False.elim ((by decide +kernel : kidW.identity ≠ kidC.identity) identity)
  · exact False.elim ((by decide +kernel : kidP.identity ≠ kidC.identity) identity)

theorem joint : GeneralNominalJointCandidates.Joint reg afterP.current kidC c.id := by
  have branchAt : GeneralNominalJointCandidates.BranchAt reg afterP.current kidC c.id journalModel :=
    ⟨c,by simp [reg],c_checked,rfl,rfl,prepared,[(1,1)],located,journal_branch⟩
  refine ⟨?_,journalModel,source_model journalModel cut_journal_models.1,branchAt,?_⟩
  · intro packet member related
    have same := List.mem_singleton.mp member
    subst packet
    have impossible := alias_identity related
    exact False.elim ((by decide +kernel : kidC.identity ≠ root.identity) impossible)
  · intro site related
    have equal := site_identity site related.1 (alias_identity related.2).symm
    subst site
    exact branchAt

theorem enabled : GeneralNominalFeedbackSteps.Installable reg afterP.current cpkt := by
  refine ⟨⟨rfl,rfl,?_,by simp [reg],rfl,located,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,joint⟩,selected,?_⟩
  · rw [sites]; simp [cpkt,containerPacket]
  · intro packet member related
    have same := List.mem_singleton.mp member
    subst packet
    have impossible := alias_identity related
    exact False.elim ((by decide +kernel : kidC.identity ≠ root.identity) impossible)
  · intro other member same
    have equal := site_role other member same.1.symm
    subst other
    exact .refl _
  · exact ⟨journalModel,source_model journalModel cut_journal_models.1,journal_branch⟩
  · intro other member same
    have equal := site_role other member same.1.symm
    subst other
    exact .refl _

private theorem int_not_nominal (arguments : List Argument) : ¬ Subtype (.base .int) (nominal 0 arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

set_option maxRecDepth 4096 in
theorem novel : ¬ GeneralNominalFeedbackSteps.Committed afterP.current cpkt := by
  intro committed
  let model := GeneralNominalOutputGrowth.finiteModel 2
  have original : GeneralNominalState.Models src model := by
    apply (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
    intro index bound
    exact GeneralNominalOutputGrowth.finite_prefix_models 2 index (by omega)
  have full := committed.1 model (source_model model original)
  have output := (GeneralNominalPacketSupport.packet_exact cpkt model).mp full |>.2.2
  change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema cpkt) model at output
  rw [schema] at output
  have condition := (output.2.1 ⟨0,.source out,.actual⟩ (by simp)).2 (model out).1 (.source out)
  change GeneralNominalCaptureMerges.Fits model
    ((GeneralNominalAllocation.capture _ _ _ _ cpkt.bindings).inputs 0) (model out).1 at condition
  rw [bindings] at condition
  have below : Subtype (model out).1 (model 2).1 := condition.2
  have above : 2 < out := GeneralNominalIdentities.source_above_seed _ _
  have denied : ∀ n, 2 < n → ¬ Subtype (model n).1 (model 2).1 := by
    intro n bound below
    have zero : 3-n = 0 := by omega
    change Subtype (GeneralNominalOutputGrowth.tower (3-n)) (GeneralNominalOutputGrowth.tower 1) at below
    rw [zero] at below
    exact int_not_nominal _ below
  exact denied out above below

noncomputable def afterC : Tracked roles := GeneralNominalDownstreamSteps.install afterP cpkt []

theorem step : GeneralNominalDownstreamSteps.Step reg root afterP afterC :=
  ⟨kidC,children_generated.1,.install cpkt [] enabled novel container_source_guard⟩

theorem formed : GeneralNominalDownstreamSteps.SourceFormed reg root afterC :=
  .update GeneralNominalDownstreamExamples.p_first_formed step

theorem actual_prefix : B4Target.Steps (GeneralNominalDownstreamSteps.Step reg root) start afterC :=
  .tail (.tail .refl GeneralNominalDownstreamExamples.p_first_step) step

theorem container_discharged : Discharged afterC.current kidC := by
  apply Discharged.packet cpkt (by simp [afterC,GeneralNominalDownstreamSteps.install,GeneralNominalSupportSteps.install,GeneralNominalFeedbackSites.install])
  intro child member
  rw [children] at member
  cases member

end Yulang.GeneralNominalBudgetContainer
