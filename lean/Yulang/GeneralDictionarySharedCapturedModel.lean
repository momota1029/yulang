import Yulang.GeneralDictionarySharedCapturedTargets

/-! A finite assignment for the captured-input proposal. Fresh compound-input
endpoints receive list int; no source assignment or output is identified with
those fresh identities. -/
namespace Yulang.GeneralDictionarySharedCapturedModel
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower)
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩
abbrev lo : Nat := (GeneralNominalAllocation.allocation (roles := roles) source registry root.identity
  capturedProposal.id producerOnInput).arguments ⟨0,by decide +kernel⟩ |>.1
abbrev hi : Nat := (GeneralNominalAllocation.allocation (roles := roles) source registry root.identity
  capturedProposal.id producerOnInput).arguments ⟨0,by decide +kernel⟩ |>.2

theorem lo_fresh (i : Nat) (h : i ≤ 2) : lo ≠ i :=
  GeneralNominalAllocation.source_initial_fresh source registry root.identity _ i h
theorem hi_fresh (i : Nat) (h : i ≤ 2) : hi ≠ i :=
  GeneralNominalAllocation.source_initial_fresh source registry root.identity _ i h

theorem target_ne_lo : target ≠ lo := by
  intro eq
  have := (GeneralNominalAllocation.source_identity source registry root.identity _ _).mp eq
  cases this

theorem target_ne_hi : target ≠ hi := by
  intro eq
  have := (GeneralNominalAllocation.source_identity source registry root.identity _ _).mp eq
  cases this

def model : GeneralNominalCommonBridge.Assignment := fun i =>
  if i = lo ∨ i = hi then (tower 1,Common.rowEmpty) else GeneralNominalOutputGrowth.finiteModel 1 i

theorem model_old (i : Nat) (h : i ≤ 2) : model i = GeneralNominalOutputGrowth.finiteModel 1 i := by
  simp [model,Ne.symm (lo_fresh i h),Ne.symm (hi_fresh i h)]
theorem model_lo : (model lo).1 = tower 1 := by simp [model]; rfl
theorem model_hi : (model hi).1 = tower 1 := by simp [model]; rfl
theorem model_target : (model target).1 = tower 0 := by
  have fresh := GeneralNominalIdentities.source_above_seed source.seed
    (GeneralNominalAllocation.origin root.identity capturedProposal.id 5 111 0)
  have above : 2 < target := fresh
  simp [model,target_ne_lo,target_ne_hi,GeneralNominalOutputGrowth.finiteModel,
    Nat.sub_eq_zero_of_le (by omega : 1+1 ≤ target)]
  rfl

theorem source_models : GeneralNominalState.Models source model := by
  apply (GeneralNominalOutputGrowthModels.source_models 1 model).mpr
  intro i bounded
  rw [model_old i (by omega),model_old (i+1) (by omega)]
  exact GeneralNominalOutputGrowth.finite_prefix_models 1 i bounded

abbrev mid : Origin := .nominal (.source 0) 0 0

theorem report_exact : GeneralNominalPacketSupport.report packet =
    { captures := [⟨0,(2,2),some origin⟩], inspected := [(0,0),(1,1)],
      checked := [(0,0),(0,0),(1,1),(2,2)],
      anchors := [(mid,(1,1)),(origin,(2,2))], tests := [(mid,.nominal 0 1)] } := by
  have inner : inspectMany source [.nominal 0 [.nominal 0 [.variables [0]]]] [(0,0)]
      (fun _ => none) 0 =
      { captures := [⟨0,(2,2),some origin⟩], inspected := [(0,0),(1,1)],
        checked := [(0,0),(1,1),(2,2)],
        anchors := [(mid,(1,1)),(origin,(2,2))], tests := [(mid,.nominal 0 1)] } := by
    simp only [inspectMany.eq_def]
    rw [inspect.eq_def]
    change Report.append
      (Report.visit (0,0) none (.nominal 0 1)
        (inspectMany source [.nominal 0 [.variables [0]]] [(1,1)]
          (fun index => some (.nominal (.source 0) 0 index)) 0)) {} = _
    rw [inspectMany.eq_def]
    dsimp only
    rw [inspect.eq_def]
    change Report.append
      (Report.visit (0,0) none (.nominal 0 1)
        (Report.append
          (Report.visit (1,1) (some mid) (.nominal 0 1)
            (inspectMany source [.variables [0]] [(2,2)]
              (fun index => some (.nominal mid 0 index)) 0))
          (inspectMany source [] [] (fun index => some (.nominal (.source 0) 0 index)) 1))) {} = _
    simp only [inspectMany.eq_def,inspect.eq_def]
    rfl
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries,inner]
  rfl

theorem canonical : GeneralCanonicalChildOrder.canonicalDeclaration capturedProposal = capturedProposal := by
  have sorted : GeneralCanonicalChildOrder.canonicalRequirements capturedProposal.requirements =
      [producerOnInput,consumerOnInput] := by
    unfold GeneralCanonicalChildOrder.canonicalRequirements
    exact List.mergeSort_of_pairwise (by decide +kernel)
  change {capturedProposal with requirements :=
    GeneralCanonicalChildOrder.canonicalRequirements capturedProposal.requirements} = capturedProposal
  rw [sorted]

theorem schema_exact : GeneralNominalPacketSupport.namedSchema packet =
    { variables := [⟨0,.nominal (.source lo) 0 0,.actual⟩,
                    ⟨0,.nominal (.source hi) 0 0,.actual⟩,⟨0,.source target,.actual⟩],
      tests := [(.source lo,.nominal 0 1),(.source hi,.nominal 0 1)] } := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical]
  simp [GeneralNominalMaterialization.rootRequests,root,capturedProposal,producerOnInput,consumerOnInput,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    List.ofFn_succ,GeneralDeclarationPatterns.normalize,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames,target,lo,hi,
    GeneralNominalDemandMerging.pointSite,source,GeneralNominalOutputGrowthModels.source,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval]


private theorem refl_equiv (t : Ty) : Equivalent t t := ⟨subtype_refl _,subtype_refl _⟩

theorem mid_seen : Observes model mid (tower 1) := by
  apply Observes.nominal (.source 0) (arguments := [.inl (tower 1)])
  · rw [model_old 0 (by omega)]
    exact refl_equiv _
  · rfl

theorem captured_seen : Observes model origin (tower 0) :=
  .nominal mid_seen (refl_equiv _) rfl

theorem mid_same (t : Ty) (seen : Observes model mid t) : Equivalent t (tower 1) :=
  nominal_observation_unique model (.argument (.source 0) 0 0) _ _ seen mid_seen

theorem captured_same (t : Ty) (seen : Observes model origin t) : Equivalent t (tower 0) :=
  nominal_observation_unique model (.argument (.argument (.source 0) 0 0) 0 0) _ _ seen captured_seen

theorem private_models : GeneralNominalState.Models packet.privateContext.state model := by
  apply (GeneralNominalPacketSupport.private_exact packet model).mpr
  refine ⟨source_models,?_,?_,?_⟩
  · rw [GeneralDictionarySharedCapturedTargets.bindings]
    intro first one last two same
    simp only [List.mem_singleton] at one two
    subst first; subst last
    exact subtype_refl _
  · rw [GeneralDictionarySharedCapturedTargets.bindings]
    change PresenceNormalForm.All _ _ []
    intro atom member; cases member
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem projections : ProjectionModels source (GeneralNominalPacketSupport.report packet) model := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨⟨_,mid_seen⟩,?_⟩
      intro actual seen
      have same := mid_same actual seen
      change Subtype (model 1).1 actual ∧ Subtype actual (model 1).1
      rw [model_old 1 (by omega)]
      exact ⟨same.2,same.1⟩
    · refine ⟨⟨_,captured_seen⟩,?_⟩
      intro actual seen
      have same := captured_same actual seen
      change Subtype (model 2).1 actual ∧ Subtype actual (model 2).1
      rw [model_old 2 (by omega)]
      exact ⟨same.2,same.1⟩
  · intro test member actual seen
    have eq := List.mem_singleton.mp member; subst test
    exact ⟨[.inl (tower 0)],rfl,mid_same actual seen⟩
  · intro first one last two _ ref eq actual seen
    have e1 := List.mem_singleton.mp one; have e2 := List.mem_singleton.mp two
    subst first; subst last
    cases eq
    have same := captured_same actual seen
    change Subtype (model 2).1 actual ∧ Subtype actual (model 2).1
    rw [model_old 2 (by omega)]
    exact ⟨same.2,same.1⟩
  · intro first one last two _ a b ea eb x y hx hy
    have e1 := List.mem_singleton.mp one; have e2 := List.mem_singleton.mp two
    subst first; subst last; cases ea; cases eb
    exact nominal_observation_unique model (.argument (.argument (.source 0) 0 0) 0 0) x y hx hy

theorem lo_seen : Observes model (.nominal (.source lo) 0 0) (tower 0) := by
  apply Observes.nominal (.source lo) (arguments := [.inl (tower 0)])
  · rw [model_lo]; exact refl_equiv _
  · rfl

theorem hi_seen : Observes model (.nominal (.source hi) 0 0) (tower 0) := by
  apply Observes.nominal (.source hi) (arguments := [.inl (tower 0)])
  · rw [model_hi]; exact refl_equiv _
  · rfl

theorem use_values (entry : GeneralNominalMaterialization.Use)
    (member : entry ∈ (GeneralNominalPacketSupport.namedSchema packet).variables) :
    entry.name = 0 ∧ entry.mode = .actual ∧
    (∃ actual, Observes model entry.origin actual) ∧
    ∀ actual, Observes model entry.origin actual → Equivalent actual (tower 0) := by
  rw [schema_exact] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨rfl,rfl,⟨_,lo_seen⟩,fun actual seen =>
      nominal_observation_unique model (.argument (.source lo) 0 0) _ _ seen lo_seen⟩
  · exact ⟨rfl,rfl,⟨_,hi_seen⟩,fun actual seen =>
      nominal_observation_unique model (.argument (.source hi) 0 0) _ _ seen hi_seen⟩
  · refine ⟨rfl,rfl,⟨_,.source target⟩,?_⟩
    intro actual seen; cases seen
    rw [model_target]; exact refl_equiv _

theorem outputs : GeneralNominalPacketSupport.Outputs packet model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    rw [schema_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨⟨_,.source lo⟩,?_⟩
      intro actual seen; cases seen
      refine ⟨[.inl (tower 0)],rfl,?_⟩
      rw [model_lo]; exact refl_equiv _
    · refine ⟨⟨_,.source hi⟩,?_⟩
      intro actual seen; cases seen
      refine ⟨[.inl (tower 0)],rfl,?_⟩
      rw [model_hi]; exact refl_equiv _
  · intro entry member
    obtain ⟨name,mode,existsValue,same⟩ := use_values entry member
    refine ⟨existsValue,?_⟩
    intro actual seen
    change GeneralNominalMaterialization.VariableHolds capturedProposal
      (GeneralNominalPacketSupport.capture packet) model entry.name entry.mode actual
    rw [name,mode]
    change GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture packet).inputs 0) actual
    rw [capture_input]
    change Subtype (model 2).1 actual ∧ Subtype actual (model 2).1
    rw [model_old 2 (by omega)]
    exact ⟨(same actual seen).2,(same actual seen).1⟩
  · intro first one last two _ _ _ a b ha hb
    have sa := (use_values first one).2.2.2 a ha
    have sb := (use_values last two).2.2.2 b hb
    exact ⟨subtype_trans sa.1 sb.2,subtype_trans sb.1 sa.2⟩
  · intro entry member captured present _ _ ref eq a b ha hb
    rw [captures] at present
    have e := List.mem_singleton.mp present; subst captured; cases eq
    have sa := (use_values entry member).2.2.2 a ha
    have sb := captured_same b hb
    exact ⟨subtype_trans sa.1 sb.2,subtype_trans sb.1 sa.2⟩

theorem branch_models : GeneralNominalRecursiveCandidates.BranchModels registry context root
    capturedProposal captured_proposal_checked [(0,0)] model :=
  ⟨private_models,projections,outputs⟩

end Yulang.GeneralDictionarySharedCapturedModel
