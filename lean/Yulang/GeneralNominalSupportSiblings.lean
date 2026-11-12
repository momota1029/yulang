import Yulang.GeneralNominalSupportGrowth

/-! A checked shared-output sibling fixture on the general nominal carrier.
`p` is P(list a) with Container(a,item=z), Wrap(a,out=z), and P(a).
`c` is Container(list t) with item=t; Wrap is the existing general example.
This module proves the actual first guarded installation and its emitted
identities. It does not assert subsequent sibling installations or divergence. -/

set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalSupportSiblings
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples
abbrev cp : Clause := ⟨100,2,[.var 0],[⟨101,1,.var 2⟩]⟩
abbrev wp : Clause := ⟨102,1,[.var 0],[⟨103,0,.var 2⟩]⟩
abbrev pp : Clause := ⟨104,0,[.var 0],[]⟩
abbrev p : Declaration := ⟨90,0,[.app 0 [.var 0]],[cp,wp,pp],[],[⟨2,100,101⟩]⟩
theorem p_checked : DeclarationChecked constructors roles p := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,Declared,roles,bareRole,binaryRole,outputRole,p,cp,wp,pp]
  · simp [Declaration.Identified,Declaration.outputNames,p,cp,wp,pp]
  · simp [Declaration.Produced,p,cp,wp,pp]
  · simp [Declaration.OutputOnly,Declaration.outputNames,p,cp,wp,pp,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,p,cp,wp,pp,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,p,cp,wp,pp]
  · intro cl member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro cl member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro cl member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> unfold ConservativeSmaller <;> decide +kernel
  · intro cl member
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact unary_descent 0 0

abbrev c : Declaration := ⟨91,2,[.app 0 [.var 0]],[],[⟨105,1,.var 0⟩],[]⟩
theorem c_checked : DeclarationChecked constructors roles c := by
  constructor
  · constructor
    · rfl
    · refine ⟨?_,?_,?_⟩
      · intro e h
        have same := List.mem_singleton.mp h
        subst e
        exact ⟨none,rfl⟩
      · intro n body present
        by_cases one : n=1
        · subst n
          exact Or.inl ⟨⟨105,1,.var 0⟩,by simp,rfl⟩
        · simp [roles,outputRole,one] at present
      · intro cl impossible; cases impossible
  · simp [Declaration.Identified,Declaration.outputNames,c]
  · simp [Declaration.Produced,c]
  · simp [Declaration.OutputOnly,Declaration.outputNames,c]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,c,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,c]
  all_goals intro cl impossible; cases impossible
abbrev reg : Registry := ⟨constructors,roles,[p,c,wrap]⟩
theorem checked : Checked reg := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  simp only [reg,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact p_checked
  · exact c_checked
  · exact wrap_checked
end Yulang.GeneralNominalSupportSiblings
namespace Yulang.GeneralNominalSupportSiblings
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (roles constructors wrap wrap_checked)
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
abbrev src := GeneralNominalOutputGrowthModels.source 1
abbrev ctx := GeneralNominalOutputGrowthModels.context 1
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev bs : List (GeneralNominalInspection.Bounds src) := [(0,0)]
abbrev pk : Packet roles := ⟨reg,ctx,GeneralNominalDemandMerging.pointSite root,p,p_checked,bs⟩
abbrev desc := GeneralNominalOutputGrowthModels.descriptor 1 (0 : Fin src.base.slots) (by decide +kernel)
theorem p_query : GeneralNominalInspection.queries src ctx.interpretation p = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,p,src,GeneralNominalOutputGrowthModels.source]
theorem p_report : report ctx p bs = captured src 0 0 0 (1,1) :=
  report_exact ctx p 0 desc rfl 0 (1,1) rfl p_query
abbrev out : Nat := GeneralNominalAllocation.source src reg root.identity
  (GeneralNominalAllocation.origin root.identity p.id 2 2 0)
theorem sorted : GeneralCanonicalChildOrder.canonicalRequirements p.requirements = [cp,wp,pp] := by
  unfold GeneralCanonicalChildOrder.canonicalRequirements
  exact List.mergeSort_of_pairwise (by decide +kernel)
theorem p_schema : generated reg ctx root p p_checked bs =
    ⟨[⟨2,.source out,.actual⟩,⟨2,.source out,.actual⟩],[],false⟩ := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration p = p := by
    change {p with requirements := GeneralCanonicalChildOrder.canonicalRequirements p.requirements} = p
    rw [sorted]
  unfold generated GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [GeneralNominalMaterialization.rootRequests,root,p,cp,wp,pp,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames,GeneralNominalAllocation.capture,out]
end Yulang.GeneralNominalSupportSiblings
namespace Yulang.GeneralNominalSupportSiblings
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (roles constructors wrap wrap_checked)
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
theorem p_material (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalMaterialization.Models src p
      (GeneralNominalAllocation.capture src reg root.identity p.id (bindings src (report ctx p bs)))
      (report ctx p bs) (generated reg ctx root p p_checked bs) model := by
  rw [p_schema,p_report]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member; cases member
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst entry
    refine ⟨⟨_,.source out⟩,?_⟩
    intro actual seen
    cases seen
    change GeneralNominalMaterialization.VariableHolds p _ model 2 .actual (model out).1
    simp only [GeneralNominalMaterialization.VariableHolds,p,Declaration.outputNames,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false,ite_true]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first hf last hl _ _ _ a b ha hb
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hf hl
    subst first; subst last
    cases ha; cases hb
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry he cap hc same
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at he
    subst entry
    have ce := List.mem_singleton.mp hc
    subst cap
    cases same

theorem p_branch (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) : pk.Holds model := by
  have base := private_models ctx reg root p 0 desc rfl 0 rfl (1,1) rfl p_query model valid
  exact ⟨base.1,base.2,p_material model⟩

theorem metadata : Metadata reg ctx := ⟨rfl,(GeneralNominalOutputGrowthModels.metadata 1).2⟩
theorem initial_source : GeneralNominalSourceFormation.InitialSource reg ctx root := by
  refine ⟨rfl,metadata,?_,?_,(GeneralNominalOutputGrowthModels.initial_source 1).below_seed,rfl⟩
  · constructor
    · intro index
      have present := GeneralNominalOutputGrowthModels.source_member 1 (0 : Fin src.base.slots)
      exact ⟨present,present⟩
    · intro output member; cases member
  · intro model valid index; exact subtype_refl _

theorem located : arguments ctx root = some bs := by decide +kernel

theorem p_prepared : Prepared reg ctx root p p_checked := by
  refine ⟨metadata,initial_source.linked,GeneralNominalSourceFormation.initial_fresh ctx initial_source root.identity,
    bs,located,?_,?_,GeneralNominalOutputGrowth.finiteModel 1,?_⟩
  · rw [p_report]; exact ⟨rfl,rfl,rfl⟩
  · exact ⟨(by intro output h; cases h),(by rw [p_schema])⟩
  · exact p_branch _ ((GeneralNominalOutputGrowthModels.source_models 1 _).mpr
      (GeneralNominalOutputGrowth.finite_prefix_models 1))

theorem root_ready : ¬ GeneralNominalState.RootPending src root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨desc,rfl⟩⟩

theorem p_survivor : Survivor reg ctx root p.id pk.children :=
  ⟨root_ready,p,by simp [reg],p_checked,rfl,rfl,bs,located,p_prepared,rfl⟩

abbrev start : GeneralNominalSupport.Tracked roles := GeneralNominalSupport.initial ctx root
private theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic start.current (GeneralNominalOutputGrowth.finiteModel 1)
    ((initial_models ctx root _).mpr ((GeneralNominalOutputGrowthModels.source_models 1 _).mpr
      (GeneralNominalOutputGrowth.finite_prefix_models 1))) (fun i => 2-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

private theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact GeneralNominalOutputGrowthModels.raw_acyclic 1 slot
      (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

private theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 reg start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact GeneralNominalOutputGrowthModels.raw_acyclic 1 visited.1
      (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem p_only (d : Declaration) (visible : d ∈ reg.declarations) (role : d.role = root.demand.role) : d=p := by
  simp only [reg,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · rfl
  · cases role
  · cases role

theorem selected_old : GeneralNominalFeedbackK2.Local reg start.current root (.selected p.id pk.children) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ ⟨p_survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,certified,role,failed,missing⟩ := pending
      have same := p_only d visible role
      subst d
      exact missing p_prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
  · intro key kids survivor
    have copy := survivor
    obtain ⟨_,d,visible,certified,identity,role,_⟩ := survivor
    have same := p_only d visible role
    subst d
    subst key
    exact ⟨rfl,survivor_children_functional reg checked ctx root p.id kids pk.children copy p_survivor⟩
end Yulang.GeneralNominalSupportSiblings
namespace Yulang.GeneralNominalSupportSiblings
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (roles constructors wrap wrap_checked)
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier
open GeneralNominalSupport GeneralNominalSupportSteps
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
theorem p_reads : readsMany src (GeneralNominalInspection.queries src ctx.interpretation p) bs = [0] := by
  rw [p_query]
  have recorded : src.nominals 0 = some desc := rfl
  simp only [bs,readsMany.eq_def,List.append_nil]
  rw [reads.eq_def,recorded]
  change 0 :: readsMany src [.variables [0]] [(1,1)] = [0]
  rw [readsMany.eq_def]
  simp only [reads.eq_def,readsMany.eq_def,List.nil_append,List.append_nil]

theorem decisions : DecisionGuard start reg root [] := by
  have head : Head src 0 (.nominal 0 1) (.nominal src.base 0 desc) := Head.nominal (snapshot := src) 0 desc rfl
  have ready : ReadyAt start [] 0 := source_ready start 0 _ _ _ head head []
  refine ⟨(by intro _ h; cases h),(fun _ => ready),?_⟩
  intro d visible role bounds loc slot member
  have same := p_only d visible role
  subst d
  have equal := Option.some.inj (located.symm.trans loc)
  subst bounds
  change slot ∈ readsMany src (GeneralNominalInspection.queries src ctx.interpretation p) bs at member
  rw [p_reads] at member
  have zero := List.mem_singleton.mp member
  subst slot
  exact ready

theorem p_guard : PacketGuard start pk [] :=
  ⟨⟨decisions.1,decisions.2.1,decisions.2.2 p (by simp [reg]) rfl bs located⟩,decisions⟩

theorem selected : GeneralNominalSupportBoundary.Local reg start root (.selected p.id pk.children) :=
  GeneralNominalSupportBoundary.selected_supported selected_old [] decisions

abbrev sigC : cp.Signature roles := p_checked.signature.2.2.2 cp (by simp [p])
abbrev sigW : wp.Signature roles := p_checked.signature.2.2.2 wp (by simp [p])
abbrev sigP : pp.Signature roles := p_checked.signature.2.2.2 pp (by simp [p])
abbrev kidC : Occurrence roles := GeneralNominalFeedbackSites.clauseChild pk cp sigC
abbrev kidW : Occurrence roles := GeneralNominalFeedbackSites.clauseChild pk wp sigW
abbrev kidP : Occurrence roles := GeneralNominalFeedbackSites.clauseChild pk pp sigP

theorem p_children : pk.children = [kidC,kidW,kidP] := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration p = p := by
    change {p with requirements := GeneralCanonicalChildOrder.canonicalRequirements p.requirements} = p
    rw [sorted]
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [GeneralDeclarationDemands.emitAll,GeneralNominalFeedbackSites.clauseChild,
    GeneralNominalFeedbackSites.frame,pk,GeneralDictionaryEmissionPlans.occurrence,kidC,kidW,kidP]

theorem enabled : GeneralNominalFeedbackSteps.Installable reg start.current pk := by
  let model := GeneralNominalOutputGrowth.finiteModel 1
  have valid := (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1)
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial,pk],by simp [reg],rfl,located,p_prepared,
    GeneralNominalFeedbackK2.selected_legacy selected_old,?_,?_,?_,?_⟩,selected_old,?_⟩
  · intro prior member; cases member
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _
  · exact ⟨model,(initial_models ..).mpr valid,p_branch model valid⟩
  · exact GeneralNominalJointCandidates.initial_joint reg ctx root p (by simp [reg]) p_checked rfl bs located p_prepared model (p_branch model valid)
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _

noncomputable def afterP : Tracked roles := GeneralNominalSupportSteps.install start pk []
theorem first_step : Step reg root start afterP := by
  refine ⟨root,.root,.install pk [] enabled ?_ p_guard⟩
  intro done
  have bad := done.2 kidC (by rw [p_children]; simp)
  cases bad

theorem first_formed : SourceFormed reg root afterP :=
  .update (.initial ctx initial_source) first_step

theorem children_generated : Generated afterP.current root kidC ∧ Generated afterP.current root kidW ∧ Generated afterP.current root kidP := by
  refine ⟨?_,?_,?_⟩
  all_goals apply Generated.child .root
  all_goals change _ ∈ [] ++ pk.children.map (fun child => (pk.site.occurrence,child))
  all_goals rw [p_children]
  all_goals simp [pk,GeneralNominalDemandMerging.pointSite]
end Yulang.GeneralNominalSupportSiblings
namespace Yulang.GeneralNominalSupportSiblings
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (roles constructors wrap wrap_checked)
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts CommonNominalFullCarrier

theorem shared_output : kidC.demand.outputs = [⟨1,out⟩] ∧ kidW.demand.outputs = [⟨0,out⟩] := ⟨rfl,rfl⟩

theorem child_inputs :
    (∀ i, kidC.demand.arguments i = (1,1)) ∧
    (∀ i, kidW.demand.arguments i = (1,1)) ∧
    (∀ i, kidP.demand.arguments i = (1,1)) := by
  have captured : pk.bindings = [(0,(1,1))] := by
    change bindings src (report ctx p bs) = _
    rw [p_report]
    rfl
  constructor
  · intro i
    have zero : i.val = 0 := by have bound:=i.isLt; change i.val<1 at bound; omega
    simp [kidC,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
      GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
      captured,GeneralNominalAllocation.occurrences,zero,cp,normalize]
  constructor
  · intro i
    have zero : i.val = 0 := by have bound:=i.isLt; change i.val<1 at bound; omega
    simp [kidW,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
      GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
      captured,GeneralNominalAllocation.occurrences,zero,wp,normalize]
  · intro i
    have zero : i.val = 0 := by have bound:=i.isLt; change i.val<1 at bound; omega
    simp [kidP,GeneralNominalFeedbackSites.clauseChild,GeneralDictionaryEmissionPlans.occurrence,
      GeneralNominalFeedbackSites.frame,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
      GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,
      captured,GeneralNominalAllocation.occurrences,zero,pp,normalize]
end Yulang.GeneralNominalSupportSiblings
