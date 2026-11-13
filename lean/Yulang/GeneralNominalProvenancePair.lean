import Yulang.GeneralNominalProvenanceSource
import Yulang.GeneralNominalValueSupport
import Yulang.GeneralNominalValueHeadCertificate

/-! The paired W/G output journal on the exact six-role source carrier.
This is a representative journal, not a claim of source reachability. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenancePair
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalSupport CommonNominalFullCarrier
open GeneralNominalValueSupport

abbrev gRoot : Occurrence roles :=
  ⟨10,⟨2,fun index => if index.val = 0 then (4,4) else if index.val = 1 then (1,1) else (6,6),
    [⟨0,5⟩],by intro output member; have same := List.mem_singleton.mp member; subst output; exact ⟨none,rfl⟩⟩⟩
abbrev gPacket : Packet roles := ⟨registry,context,GeneralNominalDemandMerging.pointSite gRoot,g,g_checked,gBounds⟩
abbrev sigC : childC.Signature roles := w_checked.signature.2.2.2 childC (by simp)
abbrev sigD : childD.Signature roles := g_checked.signature.2.2.2 childD (by simp)
abbrev cRoot : Occurrence roles := GeneralNominalFeedbackSites.clauseChild wPacket childC sigC
abbrev dRoot : Occurrence roles := GeneralNominalFeedbackSites.clauseChild gPacket childD sigD
abbrev wOutput : Nat := GeneralNominalAllocation.source state registry wRoot.identity
  (GeneralNominalAllocation.origin wRoot.identity w.id 2 3 0)
abbrev gOutput : Nat := GeneralNominalAllocation.source state registry gRoot.identity
  (GeneralNominalAllocation.origin gRoot.identity g.id 2 3 0)

abbrev branchReport (outer inner other : Fin 8) : Report state where
  captures := [⟨0,(inner,inner),some (.nominal (.source outer.val) 0 0)⟩,
    ⟨1,(other,other),none⟩,⟨2,(6,6),none⟩]
  inspected := [(outer,outer)]
  checked := [(outer,outer),(other,other),(6,6),(outer,outer),(inner,inner),(other,other),(6,6)]
  anchors := [(.nominal (.source outer.val) 0 0,(inner,inner))]

theorem w_report : GeneralNominalPacketSupport.report wPacket = branchReport 1 2 4 := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [w_queries]
  simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,wBounds,state,entries,listDescriptor,boxDescriptor,branchReport]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]

theorem g_report : GeneralNominalPacketSupport.report gPacket = branchReport 4 5 1 := by
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [g_queries]
  simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,gBounds,state,entries,listDescriptor,boxDescriptor,branchReport]
  repeat first
    | rw [inspectMany.eq_def]
    | rw [inspect.eq_def]
    | simp [Report.visit,Report.append,typeArguments,block,context,state,entries,listDescriptor,boxDescriptor,bindings]

theorem w_packet_bindings : wPacket.bindings = [(0,(2,2)),(1,(4,4)),(2,(6,6))] := w_bindings

theorem g_packet_bindings : gPacket.bindings = [(0,(5,5)),(1,(1,1)),(2,(6,6))] := g_bindings

theorem w_children : wPacket.children = [cRoot] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,GeneralNominalFeedbackSites.frame,
    wPacket,GeneralDictionaryEmissionPlans.occurrence,cRoot]

theorem g_children : gPacket.children = [dRoot] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,GeneralNominalFeedbackSites.frame,
    gPacket,GeneralDictionaryEmissionPlans.occurrence,dRoot]

theorem c_inputs (index : Fin 2) : cRoot.demand.arguments index = if index.val = 0 then (4,4) else (6,6) := by
  have cases : index = 0 ∨ index = 1 := by
    have h := index.isLt
    have : index.val = 0 ∨ index.val = 1 := by omega
    exact this.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases cases with rfl | rfl
  all_goals simp [cRoot,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
    w_packet_bindings,GeneralNominalAllocation.occurrences,childC,GeneralDeclarationPatterns.normalize]

theorem d_inputs (index : Fin 2) : dRoot.demand.arguments index = if index.val = 0 then (1,1) else (6,6) := by
  have cases : index = 0 ∨ index = 1 := by
    have h := index.isLt
    have : index.val = 0 ∨ index.val = 1 := by omega
    exact this.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases cases with rfl | rfl
  all_goals simp [dRoot,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
    GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
    g_packet_bindings,GeneralNominalAllocation.occurrences,childD,GeneralDeclarationPatterns.normalize]

theorem w_schema : GeneralNominalPacketSupport.namedSchema wPacket =
    ⟨[⟨3,.nominal (.source 2) 0 0,.actual⟩,⟨3,.source wOutput,.actual⟩],[(.source 2,.nominal 0 1)],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated registry context wRoot w w_checked wBounds = _
  unfold GeneralNominalRecursiveCandidates.generated
  rw [w_bindings]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,interpretation,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
    wOutput,GeneralNominalAllocation.allocation,state,constructors,GeneralDeclarationExamples.constructors]

theorem g_schema : GeneralNominalPacketSupport.namedSchema gPacket =
    ⟨[⟨3,.nominal (.source 5) 0 0,.actual⟩,⟨3,.source gOutput,.actual⟩],[(.source 5,.nominal 0 1)],false⟩ := by
  change GeneralNominalRecursiveCandidates.generated registry context gRoot g g_checked gBounds = _
  unfold GeneralNominalRecursiveCandidates.generated
  rw [g_bindings]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,interpretation,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
    gOutput,GeneralNominalAllocation.allocation,state,constructors,GeneralDeclarationExamples.constructors]


private theorem branch_projection (outer inner other : Fin 8)
    (recorded : state.nominals outer = some (listDescriptor inner))
    (assignment : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state assignment) :
    ProjectionModels state (branchReport outer inner other) assignment := by
  have argument := nominal_argument_bounds state assignment valid outer (listDescriptor inner) recorded 0 (inner,inner) rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    have same := List.mem_singleton.mp member; subst anchor
    exact argument
  · intro test member; cases member
  · intro first one last two same origin seen actual observed
    simp only [branchReport,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals dsimp only at same seen
    all_goals try cases same
    all_goals try (solve | cases seen)
    have equal := Option.some.inj seen
    subst origin
    exact argument.2 actual observed
  · intro first one last two same a b ha hb x y hx hy
    simp only [branchReport,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals dsimp only at same ha hb
    all_goals try cases same
    all_goals try (solve | cases ha | cases hb)
    have ea := Option.some.inj ha
    have eb := Option.some.inj hb
    subst a; subst b
    exact nominal_observation_unique assignment (.argument (.source outer.val) 0 0) x y hx hy

theorem w_inputs (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) : GeneralNominalPacketSupport.Inputs wPacket assignment := by
  refine ⟨?_,?_,?_⟩
  · unfold GeneralNominalPacketSupport.Ordinary
    rw [w_packet_bindings,w_report]
    simp [GeneralNominalAllocation.Compatible,GeneralNominalAllocation.merges,Declaration.inputNames,
      Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
      GeneralNominalAllocation.occurrences,selfChecks,branchReport,PresenceNormalForm.All,
      PresenceNormalForm.Atom.Holds,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,subtype_refl]
  · rw [w_report]
    exact branch_projection 1 2 4 rfl assignment valid
  · have empty : GeneralNominalPacketSupport.inputSchema wPacket = {} := by
      unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests GeneralCanonicalChildOrder.canonicalEmit
      simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
      simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,
        List.ofFn_succ,GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated]
    rw [empty]
    exact GeneralNominalMaterialization.empty_models ..

theorem g_inputs (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) : GeneralNominalPacketSupport.Inputs gPacket assignment := by
  refine ⟨?_,?_,?_⟩
  · unfold GeneralNominalPacketSupport.Ordinary
    rw [g_packet_bindings,g_report]
    simp [GeneralNominalAllocation.Compatible,GeneralNominalAllocation.merges,Declaration.inputNames,
      Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
      GeneralNominalAllocation.occurrences,selfChecks,branchReport,PresenceNormalForm.All,
      PresenceNormalForm.Atom.Holds,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,subtype_refl]
  · rw [g_report]
    exact branch_projection 4 5 1 rfl assignment valid
  · have empty : GeneralNominalPacketSupport.inputSchema gPacket = {} := by
      unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests GeneralCanonicalChildOrder.canonicalEmit
      simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
      simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralNominalMaterialization.inputRequests,
        List.ofFn_succ,GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated]
    rw [empty]
    exact GeneralNominalMaterialization.empty_models ..


private theorem output_models (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (parent output : Nat) (assignment : GeneralNominalCommonBridge.Assignment)
    (outputOnly : 3 ∈ declaration.outputNames) (target : capture.outputs 3 = output)
    (noCapture : ∀ captured ∈ report.captures, 3 ≠ captured.name)
    (equation : Equivalent (assignment parent).1 (nominal 0 [.inl (assignment output).1])) :
    GeneralNominalMaterialization.Models state declaration capture report
      ⟨[⟨3,.nominal (.source parent) 0 0,.actual⟩,⟨3,.source output,.actual⟩],[(.source parent,.nominal 0 1)],false⟩ assignment := by
  have observed : Observes assignment (.nominal (.source parent) 0 0) (assignment output).1 :=
    .nominal (.source _) equation rfl
  have unique : ∀ actual, Observes assignment (.nominal (.source parent) 0 0) actual →
      Equivalent actual (assignment output).1 := fun actual seen =>
    nominal_observation_unique assignment (.argument (.source parent) 0 0) actual _ seen observed
  have all : ∀ use ∈ [({name := 3,origin := .nominal (.source parent) 0 0,mode := .actual} : GeneralNominalMaterialization.Use),
      ⟨3,.source output,.actual⟩], ∀ actual, Observes assignment use.origin actual → Equivalent actual (assignment output).1 := by
    intro use member actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact unique actual seen
    · cases seen; exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member; subst test
    exact ⟨⟨_,.source _⟩,fun actual seen => by cases seen; exact ⟨_,rfl,equation⟩⟩
  · intro use member
    have result := all use member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨⟨_,observed⟩,?_⟩
      intro actual seen
      simpa only [GeneralNominalMaterialization.VariableHolds,ite_eq_left outputOnly,target] using unique actual seen
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      simpa only [GeneralNominalMaterialization.VariableHolds,ite_eq_left outputOnly,target] using
        (show Equivalent (assignment output).1 (assignment output).1 from ⟨subtype_refl _,subtype_refl _⟩)
  · intro first one last two _ _ _ a b ha hb
    exact ⟨subtype_trans (all first one a ha).1 (all last two b hb).2,
      subtype_trans (all last two b hb).1 (all first one a ha).2⟩
  · intro use member captured present same _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact False.elim (noCapture captured present same)

theorem w_outputs (assignment : GeneralNominalCommonBridge.Assignment)
    (equation : Equivalent (assignment 2).1 (nominal 0 [.inl (assignment wOutput).1])) :
    GeneralNominalPacketSupport.Outputs wPacket assignment := by
  unfold GeneralNominalPacketSupport.Outputs
  rw [w_schema,w_report]
  apply output_models _ _ _ _ _ assignment (by simp [Declaration.outputNames,w,childC]) rfl ?_ equation
  intro captured member
  simp only [branchReport,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem g_outputs (assignment : GeneralNominalCommonBridge.Assignment)
    (equation : Equivalent (assignment 5).1 (nominal 0 [.inl (assignment gOutput).1])) :
    GeneralNominalPacketSupport.Outputs gPacket assignment := by
  unfold GeneralNominalPacketSupport.Outputs
  rw [g_schema,g_report]
  apply output_models _ _ _ _ _ assignment (by simp [Declaration.outputNames,g,childD]) rfl ?_ equation
  intro captured member
  simp only [branchReport,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

private theorem output_equation (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (parent output : Nat) (assignment : GeneralNominalCommonBridge.Assignment)
    (outputOnly : 3 ∈ declaration.outputNames) (target : capture.outputs 3 = output)
    (valid : GeneralNominalMaterialization.Models state declaration capture report
      ⟨[⟨3,.nominal (.source parent) 0 0,.actual⟩,⟨3,.source output,.actual⟩],[(.source parent,.nominal 0 1)],false⟩ assignment) :
    Equivalent (assignment parent).1 (nominal 0 [.inl (assignment output).1]) := by
  obtain ⟨arguments,size,equal⟩ := (valid.1 (.source parent,.nominal 0 1) (by simp)).2 _ (.source _)
  have projected := valid.2.1 ⟨3,.nominal (.source parent) 0 0,.actual⟩ (by simp)
  cases arguments with
  | nil => cases size
  | cons argument rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
    subst rest
    cases argument with
    | inl value =>
      have captured := projected.2 value (.nominal (.source _) equal rfl)
      simp only [GeneralNominalMaterialization.VariableHolds,ite_eq_left outputOnly,target] at captured
      have congruence := GeneralNominalState.singleton_nominal_congr 0 _ _ captured
      exact ⟨subtype_trans equal.1 congruence.1,subtype_trans congruence.2 equal.2⟩
    | inr row =>
      obtain ⟨actual,seen⟩ := projected.1
      cases seen with
      | nominal previous compared found =>
        cases previous
        have incompatible := ((nominal_regular_invariant_exact _ _ _ _).mp
          (subtype_trans equal.2 compared.1)).2.2 0 (.inr row) (.inl actual) rfl found
        exact False.elim incompatible

theorem w_equation (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalPacketSupport.Outputs wPacket assignment) :
    Equivalent (assignment 2).1 (nominal 0 [.inl (assignment wOutput).1]) := by
  unfold GeneralNominalPacketSupport.Outputs at valid
  rw [w_schema] at valid
  exact output_equation _ _ _ _ _ assignment (by simp [Declaration.outputNames,w,childC]) rfl valid

theorem g_equation (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalPacketSupport.Outputs gPacket assignment) :
    Equivalent (assignment 5).1 (nominal 0 [.inl (assignment gOutput).1]) := by
  unfold GeneralNominalPacketSupport.Outputs at valid
  rw [g_schema] at valid
  exact output_equation _ _ _ _ _ assignment (by simp [Declaration.outputNames,g,childD]) rfl valid


/-- Both emitted child sites and all ordinary/named packet facts are retained.
The separate source-reachability bridge is not part of this definition. -/
noncomputable def journal : Tracked roles where
  source := context
  current := {
    context := context
    packets := [wPacket,gPacket]
    sites := [wPacket.site,gPacket.site] ++ (GeneralNominalFeedbackSites.emitted wPacket).sites ++
      (GeneralNominalFeedbackSites.emitted gPacket).sites
    edges := [(wRoot,cRoot),(gRoot,dRoot)] }
  facts := [.inputs wPacket [],.outputs wPacket [],.inputs gPacket [],.outputs gPacket []]

theorem w_output_above : 7 < wOutput := GeneralNominalIdentities.source_above_seed _ _
theorem g_output_above : 7 < gOutput := GeneralNominalIdentities.source_above_seed _ _

private theorem model_above (a b u : Ty) (identity : Nat) (above : 7 < identity) :
    (model a b u identity).1 = .base .int := by
  have equal : identity = (identity - 8) + 8 := by omega
  rw [equal]
  rfl

abbrev intList : Ty := nominal 0 [.inl (.base .int)]
abbrev cutW := model (.base .int) intList (.base .str)
abbrev cutG := model intList (.base .int) (.base .str)
abbrev fullModel := model intList intList (.base .str)

theorem cut_w : CutModel journal wRoot cutW := by
  refine ⟨source_models _ _ _,?_⟩
  intro fact member absent
  simp only [journal,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact w_inputs _ (source_models _ _ _)
  · exact False.elim (absent (by simp [Fact.dependencies,GeneralNominalDemandMerging.pointSite]))
  · exact g_inputs _ (source_models _ _ _)
  · apply g_outputs
    have above := model_above (.base .int) intList (.base .str) gOutput g_output_above
    change Equivalent intList (nominal 0 [.inl (cutW gOutput).1])
    rw [above]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem cut_g : CutModel journal gRoot cutG := by
  refine ⟨source_models _ _ _,?_⟩
  intro fact member absent
  simp only [journal,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact w_inputs _ (source_models _ _ _)
  · apply w_outputs
    have above := model_above intList (.base .int) (.base .str) wOutput w_output_above
    change Equivalent intList (nominal 0 [.inl (cutG wOutput).1])
    rw [above]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact g_inputs _ (source_models _ _ _)
  · exact False.elim (absent (by simp [Fact.dependencies,GeneralNominalDemandMerging.pointSite]))

theorem a_necessary (support : List (Occurrence roles))
    (head : HeadSupported journal support 2 (.nominal 0 1)) : wRoot ∈ support :=
  nominal_support_requires_producer journal wRoot cutW cut_w 2 0 1 rfl support head

theorem b_necessary (support : List (Occurrence roles))
    (head : HeadSupported journal support 5 (.nominal 0 1)) : gRoot ∈ support :=
  nominal_support_requires_producer journal gRoot cutG cut_g 5 0 1 rfl support head

theorem a_available : Available journal 2 (.nominal 0 1) := by
  apply GeneralNominalValueHeadCertificate.of_nominal_equation journal (GeneralNominalSupportChoices.dependencyPool journal) 2 wOutput 0
    (by have above := w_output_above; omega)
  intro assignment slice
  have valid := (GeneralNominalDownstreamSupport.pool_exact journal assignment).mp slice
  exact w_equation assignment (valid.2 (.outputs wPacket []) (by simp [journal]))

theorem b_available : Available journal 5 (.nominal 0 1) := by
  apply GeneralNominalValueHeadCertificate.of_nominal_equation journal (GeneralNominalSupportChoices.dependencyPool journal) 5 gOutput 0
    (by have above := g_output_above; omega)
  intro assignment slice
  have valid := (GeneralNominalDownstreamSupport.pool_exact journal assignment).mp slice
  exact g_equation assignment (valid.2 (.outputs gPacket []) (by simp [journal]))

theorem full_models : Models journal.current fullModel := by
  have valid : GeneralNominalState.Models state fullModel := source_models _ _ _
  have wHolds : wPacket.Holds fullModel := by
    apply (GeneralNominalPacketSupport.packet_exact wPacket fullModel).mpr
    refine ⟨valid,w_inputs _ valid,w_outputs _ ?_⟩
    have above := model_above intList intList (.base .str) wOutput w_output_above
    change Equivalent intList (nominal 0 [.inl (fullModel wOutput).1])
    rw [above]
    exact ⟨subtype_refl _,subtype_refl _⟩
  have gHolds : gPacket.Holds fullModel := by
    apply (GeneralNominalPacketSupport.packet_exact gPacket fullModel).mpr
    refine ⟨valid,g_inputs _ valid,g_outputs _ ?_⟩
    have above := model_above intList intList (.base .str) gOutput g_output_above
    change Equivalent intList (nominal 0 [.inl (fullModel gOutput).1])
    rw [above]
    exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨valid,?_,?_⟩
  · intro packet member
    simp only [journal,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact wHolds
    · exact gHolds
  · intro site member
    change site ∈ [wPacket.site,gPacket.site] ++ (GeneralNominalFeedbackSites.emitted wPacket).sites ++
      (GeneralNominalFeedbackSites.emitted gPacket).sites at member
    rcases List.mem_append.mp member with earlier | generated
    · rcases List.mem_append.mp earlier with original | generated
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at original
        rcases original with rfl | rfl
        · exact GeneralNominalSaturationState.point_holds _ _
        · exact GeneralNominalSaturationState.point_holds _ _
      · exact (GeneralNominalFeedbackSites.emitted wPacket).sound fullModel wHolds site generated
    · exact (GeneralNominalFeedbackSites.emitted gPacket).sound fullModel gHolds site generated

theorem no_discharged (focus : Occurrence roles) : ¬ Discharged journal.current focus := by
  intro discharged
  induction discharged with
  | packet packet member children ih =>
    simp only [journal,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ih cRoot (by rw [w_children]; simp)
    · exact ih dRoot (by rw [g_children]; simp)
  | alias first last one two related prior ih => exact ih

theorem w_c_waiting : Waiting journal.current wRoot cRoot :=
  .child (.root (no_discharged wRoot)) (by simp [journal]) (no_discharged cRoot)

theorem g_d_waiting : Waiting journal.current gRoot dRoot :=
  .child (.root (no_discharged gRoot)) (by simp [journal]) (no_discharged dRoot)

theorem w_c_proper : ProperWaiting journal.current wRoot cRoot :=
  ⟨wRoot,cRoot,.root (no_discharged wRoot),by simp [journal],no_discharged cRoot,.root (no_discharged cRoot)⟩

theorem g_d_proper : ProperWaiting journal.current gRoot dRoot :=
  ⟨gRoot,dRoot,.root (no_discharged gRoot),by simp [journal],no_discharged dRoot,.root (no_discharged dRoot)⟩

theorem c_to_b : GeneralNominalFeedbackK2.Path journal.current (cRoot.demand.arguments (0 : Fin 2)).1 5 := by
  rw [c_inputs]
  apply GeneralNominalFeedbackK2.Path.cons (middle := 5) ?_ (.nil 5)
  refine ⟨source_member 4,source_member 5,Or.inr ?_⟩
  exact GeneralNominalFeedbackK2.endpoint_argument journal.current (4 : Fin 8) (5 : Fin 8) (5 : Fin 8) (listDescriptor 5) rfl 0 rfl
    (GeneralNominalFeedbackK2.equal_refl _ _)

theorem d_to_a : GeneralNominalFeedbackK2.Path journal.current (dRoot.demand.arguments (0 : Fin 2)).1 2 := by
  rw [d_inputs]
  apply GeneralNominalFeedbackK2.Path.cons (middle := 2) ?_ (.nil 2)
  refine ⟨source_member 1,source_member 2,Or.inr ?_⟩
  exact GeneralNominalFeedbackK2.endpoint_argument journal.current (1 : Fin 8) (2 : Fin 8) (2 : Fin 8) (listDescriptor 2) rfl 0 rfl
    (GeneralNominalFeedbackK2.equal_refl _ _)

theorem pair_not_grounded : ¬ Grounded registry journal wRoot ∧ ¬ Grounded registry journal gRoot := by
  apply mutual_value_trap registry journal wRoot gRoot
  · intro producer _
    exact no_discharged producer
  · intro producer member
    rcases member with rfl | rfl
    · refine ⟨cRoot,w_c_waiting,no_discharged cRoot,5,.nominal 0 1,
        .value w_c_proper journal.current .current (0 : Fin 2) c_to_b (.nominal 0 1) b_available,?_⟩
      intro support head
      exact ⟨gRoot,b_necessary support head,Or.inr rfl⟩
    · refine ⟨dRoot,g_d_waiting,no_discharged dRoot,2,.nominal 0 1,
        .value g_d_proper journal.current .current (0 : Fin 2) d_to_a (.nominal 0 1) a_available,?_⟩
      intro support head
      exact ⟨wRoot,a_necessary support head,Or.inl rfl⟩

theorem a_blocked (support : List (Occurrence roles)) (allowed : Supported registry journal support) :
    ¬ HeadSupported journal support 2 (.nominal 0 1) :=
  fun head => pair_not_grounded.1 (allowed wRoot (a_necessary support head))

theorem b_blocked (support : List (Occurrence roles)) (allowed : Supported registry journal support) :
    ¬ HeadSupported journal support 5 (.nominal 0 1) :=
  fun head => pair_not_grounded.2 (allowed gRoot (b_necessary support head))

end Yulang.GeneralNominalProvenancePair
