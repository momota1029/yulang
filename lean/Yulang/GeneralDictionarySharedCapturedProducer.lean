import Yulang.GeneralDictionarySharedCapturedRefresh

/-! Exact next producer packet, finite repeated-capture BranchModels witness,
and associated-output consequence. This module does not assert Prepared,
Installable, or a producer installation. -/
namespace Yulang.GeneralDictionarySharedCapturedProducer
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedRefresh
open GeneralDeclarationExamples (roles)

abbrev declaration := GeneralDictionaryRecursiveObstruction.declaration
noncomputable abbrev candidate : Packet roles :=
  ⟨registry,refreshedContext,GeneralNominalSharedEmission.childSite packet producer,
    declaration,GeneralDictionaryRecursiveObstruction.declaration_checked,[(3,4)]⟩

theorem queries : GeneralNominalInspection.queries snapshot context.interpretation declaration =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem bounds : GeneralNominalRecursiveCandidates.arguments refreshedContext producer = some [(3,4)] := by
  have left := (GeneralDictionaryBinderLocations.sourceSlot_exact base lo (3 : Fin 5)).mpr rfl
  have right := (GeneralDictionaryBinderLocations.sourceSlot_exact base hi (4 : Fin 5)).mpr rfl
  have args : List.ofFn producer.demand.arguments = [(lo,hi)] := by
    rw [show producer.demand.arguments = fun _ => (lo,hi) from
      funext GeneralDictionarySharedCapturedInstallation.producer_inputs]
    rfl
  change GeneralCandidateBoundaryParts.locate base (List.ofFn producer.demand.arguments) = _
  rw [args]
  simp [GeneralCandidateBoundaryParts.locate,left,right,Option.bind]

abbrev leftOrigin : Origin := .nominal (.source lo) 0 0
abbrev rightOrigin : Origin := .nominal (.source hi) 0 0

theorem report_exact : GeneralNominalPacketSupport.report candidate =
    { captures := [⟨0,(2,2),some leftOrigin⟩,⟨0,(2,2),some rightOrigin⟩],
      inspected := [(3,4)], checked := [(3,4),(3,4),(2,2),(2,2)],
      anchors := [(leftOrigin,(2,2)),(rightOrigin,(2,2))] } := by
  have inner : inspectMany snapshot [.nominal 0 [.variables [0]]] [(3,4)] (fun _ => none) 0 =
      { captures := [⟨0,(2,2),some leftOrigin⟩,⟨0,(2,2),some rightOrigin⟩],
        inspected := [(3,4)], checked := [(3,4),(2,2),(2,2)],
        anchors := [(leftOrigin,(2,2)),(rightOrigin,(2,2))] } := by
    simp only [inspectMany.eq_def]
    rw [inspect.eq_def]
    change Report.append
      (Report.visit (3,4) none (.nominal 0 1)
        ((inspectMany snapshot [.variables [0]] [(2,2)]
          (fun index => some (.nominal (.source lo) 0 index)) 0).append
         (inspectMany snapshot [.variables [0]] [(2,2)]
          (fun index => some (.nominal (.source hi) 0 index)) 0))) {} = _
    simp only [inspectMany.eq_def,inspect.eq_def]
    rfl
  unfold GeneralNominalPacketSupport.report GeneralNominalRecursiveCandidates.report
  rw [queries,inner]
  rfl

theorem schema_exact : GeneralNominalPacketSupport.namedSchema candidate =
    { tests := [(.source target,.scalar .int)] } := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
    change {declaration with requirements := GeneralCanonicalChildOrder.canonicalRequirements []} = declaration
    simp [GeneralCanonicalChildOrder.canonicalRequirements]
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [declaration,GeneralDictionaryRecursiveObstruction.declaration,
    GeneralNominalMaterialization.rootRequests,GeneralDictionaryRecursiveObstruction.equation,
    producer_output,GeneralDeclarationDemands.emitAll,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
    GeneralDeclarationPatterns.normalize,GeneralNominalSharedEmission.childSite,
    GeneralDeclarationPatterns.normalizeArgs]

theorem candidate_bindings : candidate.bindings = [(0,(2,2)),(0,(2,2))] := by
  change GeneralNominalRecursiveInspection.bindings snapshot (GeneralNominalPacketSupport.report candidate) = _
  rw [report_exact]
  rfl

theorem allocated_value (purpose owner position : Nat) :
    (model (GeneralNominalAllocation.source snapshot registry producer.identity
      (GeneralNominalAllocation.origin producer.identity declaration.id purpose owner position))).1 =
      GeneralNominalOutputGrowth.tower 0 := by
  let key := GeneralNominalAllocation.origin producer.identity declaration.id purpose owner position
  let identity := GeneralNominalAllocation.source snapshot registry producer.identity key
  have above : 2 < identity := GeneralNominalIdentities.source_above_seed 2 key
  have prodAbove : 2 < producer.identity :=
    GeneralNominalIdentities.source_above_seed 2
      (GeneralNominalAllocation.origin root.identity capturedProposal.id 6 producerOnInput.id 0)
  have notLo : identity ≠ lo := by
    intro same
    have eq := (GeneralNominalAllocation.source_identity source registry root.identity key
      (GeneralNominalAllocation.origin root.identity capturedProposal.id 3 producerOnInput.id 0)).mp same
    have zero := congrArg Prod.fst eq
    change producer.identity = 0 at zero
    omega
  have notHi : identity ≠ hi := by
    intro same
    have eq := (GeneralNominalAllocation.source_identity source registry root.identity key
      (GeneralNominalAllocation.origin root.identity capturedProposal.id 4 producerOnInput.id 0)).mp same
    have zero := congrArg Prod.fst eq
    change producer.identity = 0 at zero
    omega
  change (model identity).1 = _
  simp [model,notLo,notHi,GeneralNominalOutputGrowth.finiteModel,
    Nat.sub_eq_zero_of_le (by omega : 1+1 ≤ identity)]
  rfl

private theorem union_idem (t : CommonNominalFullCarrier.Ty) :
    CommonNominalFullCarrier.Equivalent t (.union t t) := by
  open CommonNominalFullCarrier in
  exact ⟨((common_union_is_join t t (.union t t)).mp (subtype_refl _)).1,
    (common_union_is_join t t t).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

private theorem inter_idem (t : CommonNominalFullCarrier.Ty) :
    CommonNominalFullCarrier.Equivalent t (.inter t t) := by
  open CommonNominalFullCarrier in
  exact ⟨(common_inter_is_meet t t t).mpr ⟨subtype_refl _,subtype_refl _⟩,
    ((common_inter_is_meet t t (.inter t t)).mp (subtype_refl _)).1⟩

theorem private_models : GeneralNominalState.Models candidate.privateContext.state model := by
  apply (GeneralNominalPacketSupport.private_exact candidate model).mpr
  refine ⟨GeneralDictionarySharedCapturedRefresh.inhabited.1,?_,?_,?_⟩
  · rw [candidate_bindings]
    intro first one last two _
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at one two
    subst first; subst last
    exact CommonNominalFullCarrier.subtype_refl _
  · rw [candidate_bindings]
    change PresenceNormalForm.All _ _
      (GeneralNominalAllocation.equations
        (GeneralNominalAllocation.source snapshot registry producer.identity
          (GeneralNominalAllocation.origin producer.identity declaration.id 0 0 0)) (.union (.var 2) (.var 2)) ++
       GeneralNominalAllocation.equations
        (GeneralNominalAllocation.source snapshot registry producer.identity
          (GeneralNominalAllocation.origin producer.identity declaration.id 1 0 0)) (.inter (.var 2) (.var 2)))
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact,allocated_value,allocated_value]
    change CommonNominalFullCarrier.Equivalent (GeneralNominalOutputGrowth.tower 0) (.union (model 2).1 (model 2).1) ∧
      CommonNominalFullCarrier.Equivalent (GeneralNominalOutputGrowth.tower 0) (.inter (model 2).1 (model 2).1)
    rw [model_old 2 (by omega)]
    exact ⟨union_idem _,inter_idem _⟩
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    rcases member with rfl | rfl | rfl
    · change CommonNominalFullCarrier.Subtype (model lo).1 (model hi).1
      rw [model_lo,model_hi]; exact CommonNominalFullCarrier.subtype_refl _
    · change CommonNominalFullCarrier.Subtype (model lo).1 (model hi).1
      rw [model_lo,model_hi]; exact CommonNominalFullCarrier.subtype_refl _
    · exact CommonNominalFullCarrier.subtype_refl _

private theorem origin_value (ref : Origin) (which : ref = leftOrigin ∨ ref = rightOrigin) :
    (∃ actual, Observes model ref actual) ∧
    ∀ actual, Observes model ref actual →
      CommonNominalFullCarrier.Equivalent actual (GeneralNominalOutputGrowth.tower 0) := by
  rcases which with rfl | rfl
  · exact ⟨⟨_,lo_seen⟩,fun actual seen => nominal_observation_unique model
      (.argument (.source lo) 0 0) _ _ seen lo_seen⟩
  · exact ⟨⟨_,hi_seen⟩,fun actual seen => nominal_observation_unique model
      (.argument (.source hi) 0 0) _ _ seen hi_seen⟩

private theorem fits_two (ref : Origin) (which : ref = leftOrigin ∨ ref = rightOrigin)
    (actual : CommonNominalFullCarrier.Ty) (seen : Observes model ref actual) :
    GeneralNominalCaptureMerges.Fits model (2,2) actual := by
  have same := (origin_value ref which).2 actual seen
  change CommonNominalFullCarrier.Subtype (model 2).1 actual ∧
    CommonNominalFullCarrier.Subtype actual (model 2).1
  rw [model_old 2 (by omega)]
  exact ⟨same.2,same.1⟩

theorem projections : ProjectionModels snapshot (GeneralNominalPacketSupport.report candidate) model := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨(origin_value leftOrigin (Or.inl rfl)).1,fits_two leftOrigin (Or.inl rfl)⟩
    · exact ⟨(origin_value rightOrigin (Or.inr rfl)).1,fits_two rightOrigin (Or.inr rfl)⟩
  · intro test member; cases member
  · intro first one last two _ ref eq actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl <;> cases eq
    · exact fits_two leftOrigin (Or.inl rfl) actual seen
    · exact fits_two leftOrigin (Or.inl rfl) actual seen
    · exact fits_two rightOrigin (Or.inr rfl) actual seen
    · exact fits_two rightOrigin (Or.inr rfl) actual seen
  · intro first one last two _ a b ea eb x y hx hy
    have va : a = leftOrigin ∨ a = rightOrigin := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at one
      rcases one with rfl | rfl <;> cases ea
      · exact Or.inl rfl
      · exact Or.inr rfl
    have vb : b = leftOrigin ∨ b = rightOrigin := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at two
      rcases two with rfl | rfl <;> cases eb
      · exact Or.inl rfl
      · exact Or.inr rfl
    have sa := (origin_value a va).2 x hx
    have sb := (origin_value b vb).2 y hy
    exact ⟨CommonNominalFullCarrier.subtype_trans sa.1 sb.2,
      CommonNominalFullCarrier.subtype_trans sb.1 sa.2⟩

theorem materialized : GeneralNominalPacketSupport.Outputs candidate model := by
  unfold GeneralNominalPacketSupport.Outputs
  rw [schema_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source target⟩,?_⟩
    intro actual seen; cases seen
    change CommonNominalFullCarrier.Equivalent (model target).1 (.base .int)
    rw [model_target]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro entry member; cases member
  · intro entry member; cases member
  · intro entry member; cases member

theorem branch_models : candidate.Holds model := ⟨private_models,projections,materialized⟩

theorem output_int (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : candidate.Holds assignment) : CommonNominalFullCarrier.Equivalent (assignment target).1 (.base .int) := by
  have material := valid.2.2
  change GeneralNominalPacketSupport.Outputs candidate assignment at material
  have member : (.source target,Test.scalar .int) ∈ (GeneralNominalPacketSupport.namedSchema candidate).tests := by
    rw [schema_exact]; exact List.mem_singleton_self _
  exact (material.1 _ member).2 _ (.source target)

theorem captured_int (assignment : GeneralNominalCommonBridge.Assignment)
    (current : Models refreshed.current assignment) (valid : candidate.Holds assignment) :
    CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int) := by
  have same := GeneralDictionarySharedCapturedInstallation.output_capture_equivalent assignment
    ((models_exact assignment).mp current)
  have output := output_int assignment valid
  exact ⟨CommonNominalFullCarrier.subtype_trans same.2 output.1,
    CommonNominalFullCarrier.subtype_trans output.2 same.1⟩

end Yulang.GeneralDictionarySharedCapturedProducer
