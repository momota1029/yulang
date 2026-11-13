import Yulang.GeneralDictionaryCapturedAliasCountermodel

/-! An all-Trusted-slices countermodel at the actual post-producer scalar
refresh. Parent inputs, producer inputs, and producer outputs all hold in the
same model with captured source 2 = str. Parent outputs are excluded by their
unsettled consumer. The cached scalar observation is therefore raw-ready but
not Shared ReadyAt. No execution semantics or guard is changed. -/
namespace Yulang.GeneralDictionaryCapturedInputCountermodel
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedGuards CommonNominalFullCarrier
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩
noncomputable abbrev model := GeneralDictionaryCapturedAliasCountermodel.model
abbrev tower := GeneralDictionarySharedCapturedNovelty.tower
abbrev finiteModel := GeneralDictionarySharedCapturedNovelty.finiteModel

theorem model_old (i : Nat) (h : i ≤ 2) : model i = finiteModel i := by
  change GeneralDictionaryCapturedAliasCountermodel.model i = _
  rw [GeneralDictionaryCapturedAliasCountermodel.old_value i h]
  exact GeneralDictionarySharedCapturedNovelty.model_old i h

theorem model_lo : (model lo).1 = tower 1 := by
  change (GeneralDictionaryCapturedAliasCountermodel.model lo).1 = _
  simp only [GeneralDictionaryCapturedAliasCountermodel.model,Ne.symm target_ne_lo,ite_false]
  exact GeneralDictionarySharedCapturedNovelty.model_lo

theorem model_hi : (model hi).1 = tower 1 := by
  change (GeneralDictionaryCapturedAliasCountermodel.model hi).1 = _
  simp only [GeneralDictionaryCapturedAliasCountermodel.model,Ne.symm target_ne_hi,ite_false]
  exact GeneralDictionarySharedCapturedNovelty.model_hi

theorem source_models : GeneralNominalState.Models source model :=
  GeneralDictionaryCapturedAliasCountermodel.source_models

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
    (member : entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables) :
    entry.name = 0 ∧ entry.mode = .actual ∧
    (∃ actual, Observes model entry.origin actual) ∧
    ∀ actual, Observes model entry.origin actual → Equivalent actual (tower 0) := by
  rw [input_schema] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl,rfl,⟨_,lo_seen⟩,fun actual seen =>
      nominal_observation_unique model (.argument (.source lo) 0 0) _ _ seen lo_seen⟩
  · exact ⟨rfl,rfl,⟨_,hi_seen⟩,fun actual seen =>
      nominal_observation_unique model (.argument (.source hi) 0 0) _ _ seen hi_seen⟩
theorem parent_materialized : GeneralNominalMaterialization.Models packet.context.state
    packet.declaration (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalPacketSupport.report packet) (GeneralNominalPacketSupport.inputSchema packet) model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    rw [input_schema] at member
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

theorem parent_inputs : GeneralNominalPacketSupport.Inputs packet model :=
  ⟨((GeneralNominalPacketSupport.private_exact packet model).mp private_models).2,
    projections,parent_materialized⟩
namespace Producer
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedRefresh
theorem allocated_value (purpose owner position : Nat) :
    (model (GeneralNominalAllocation.source snapshot registry producer.identity
      (GeneralNominalAllocation.origin producer.identity declaration.id purpose owner position))).1 =
      tower 0 := by
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
  have notTarget : identity ≠ target := by
    intro same
    have eq := (GeneralNominalAllocation.source_identity source registry root.identity key
      (GeneralNominalAllocation.origin root.identity capturedProposal.id 5 111 0)).mp same
    have zero := congrArg Prod.fst eq
    change producer.identity = 0 at zero
    omega
  change (GeneralDictionaryCapturedAliasCountermodel.model identity).1 = _
  simp only [GeneralDictionaryCapturedAliasCountermodel.model,notTarget,ite_false]
  change (GeneralDictionarySharedCapturedNovelty.model identity).1 = _
  simp [GeneralDictionarySharedCapturedNovelty.model,notLo,notHi,
    GeneralDictionarySharedCapturedNovelty.finiteModel,
    Nat.sub_eq_zero_of_le (by omega : 2 ≤ identity)]
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

theorem ordinary : GeneralNominalPacketSupport.Ordinary candidate model := by
  refine ⟨?_,?_,?_⟩
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
    change CommonNominalFullCarrier.Equivalent (tower 0) (.union (model 2).1 (model 2).1) ∧
      CommonNominalFullCarrier.Equivalent (tower 0) (.inter (model 2).1 (model 2).1)
    rw [model_old 2 (by omega)]
    exact ⟨union_idem _,inter_idem _⟩
  · rw [GeneralDictionarySharedCapturedProducer.report_exact]
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
      CommonNominalFullCarrier.Equivalent actual (tower 0) := by
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
  rw [GeneralDictionarySharedCapturedProducer.report_exact]
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

theorem inputs : GeneralNominalPacketSupport.Inputs candidate model :=
  ⟨ordinary,projections,GeneralNominalPacketSupport.outputs_inputs candidate model
    GeneralDictionaryCapturedAliasCountermodel.output_models⟩
end Producer

open GeneralNominalSupport GeneralDictionarySharedCapturedResumption
open GeneralDeclarationExamples (roles)
open GeneralDictionarySharedCapturedProducer

theorem trusted_member_recorded {rs : Roles.RoleDecls} {state : Tracked rs}
    {facts : List (Fact rs)} {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    {fact : Fact rs} (member : fact ∈ facts) : fact ∈ state.facts := by
  induction trusted with
  | source => cases member
  | input p support _ present _ _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact present
    · exact ih tail
  | output p support cert target term _ present _ _ _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact present
    · exact ih tail
  | merge first last support _ present _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact present
    · exact ih tail

theorem recorded_except_parent {fact : Fact roles} (member : fact ∈ observed.facts)
    (notParent : ∀ support, fact ≠ Fact.outputs packet support) : fact.Holds model := by
  change fact ∈ GeneralNominalSupportChoices.installedFacts
    GeneralDictionarySharedCapturedRefresh.refreshed candidate ++
    GeneralDictionarySharedCapturedInstallation.after.facts at member
  rw [GeneralDictionarySharedCapturedInputReady.facts] at member
  rcases List.mem_append.mp member with new | old
  · obtain ⟨support,_,entry⟩ := List.mem_flatMap.mp new
    simp only [List.mem_cons,List.not_mem_nil,or_false] at entry
    rcases entry with rfl | rfl
    · exact Producer.inputs
    · exact GeneralDictionaryCapturedAliasCountermodel.output_models
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at old
    rcases old with rfl | rfl
    · exact parent_inputs
    · exact False.elim (notParent [] rfl)

theorem every_trusted_slice {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks) :
    GeneralNominalSharedSupport.Models observed facts model := by
  refine ⟨source_models,?_⟩
  intro fact member
  apply recorded_except_parent (trusted_member_recorded trusted member)
  intro support equal
  subst fact
  exact GeneralDictionaryCapturedSettlementBoundary.parent_not_trusted trusted support member

theorem no_trusted_scalar_entailment {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks) :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed facts m →
      Equivalent (m 2).1 (.base .int)) := by
  intro entails
  exact GeneralDictionaryCapturedAliasCountermodel.captured_not_int
    (entails model (every_trusted_slice trusted))

open GeneralDictionaryCapturedScalarRefresh

theorem current_head_scalar {identity : Nat} {test : Test} {observation : GeneralCanonicalObservations.Observation}
    (head : Head observed.current.context.state identity test observation)
    (equal : identity = 2) : test = .scalar .int := by
  cases head with
  | scalar slot base recorded =>
    change (if slot.val = 2 then GeneralNormalizedObservation.Head.scalar .int else .deferred .unresolved) = .scalar base at recorded
    split at recorded
    · cases recorded; rfl
    · cases recorded
  | structural slot kind children recorded =>
    change (if slot.val = 2 then GeneralNormalizedObservation.Head.scalar .int else .deferred .unresolved) = .structural kind children at recorded
    split at recorded <;> cases recorded
  | nominal slot descriptor recorded =>
    have slotEq : slot = (2 : Fin 5) :=
      GeneralDictionarySharedCapturedRefresh.identifiers_injective equal
    subst slot
    change none = some descriptor at recorded
    cases recorded

theorem scalar_head_holds {snapshot : GeneralNominalState.State} {identity : Nat}
    {base : Inference.Base} {observation : GeneralCanonicalObservations.Observation}
    {m : GeneralNominalCommonBridge.Assignment}
    (head : Head snapshot identity (.scalar base) observation)
    (holds : observation.Holds m) : Equivalent (m identity).1 (.base base) := by
  cases head with
  | scalar slot base recorded => exact holds

theorem consumer_input_not_ready : ¬ GeneralNominalSharedSupport.ReadyAt observed 2 := by
  rintro ⟨test,observation,head,facts,readbacks,trusted,snapshot,witness,seen,entailed⟩
  have same := current_head_scalar head rfl
  subst test
  apply no_trusted_scalar_entailment trusted
  intro m valid
  exact scalar_head_holds seen (entailed m valid)

theorem consumer_decision_guard_absent :
    ¬ GeneralNominalSharedSupport.DecisionGuard registry observed consumer := by
  intro guard
  have ready := guard.1 (0 : Fin 1)
  have equal := congrArg Prod.fst
    (GeneralDictionarySharedCapturedTargets.consumer_input (0 : Fin 1))
  exact consumer_input_not_ready (Eq.mp (congrArg
    (GeneralNominalSharedSupport.ReadyAt observed) equal) ready)

theorem raw_ready_not_trusted :
    ¬ GeneralNominalState.RootPending observed.current.context.state consumer.demand ∧
    ¬ GeneralNominalSharedSupport.ReadyAt observed 2 :=
  ⟨GeneralDictionarySharedCapturedResumption.consumer_raw_ready,consumer_input_not_ready⟩
end Yulang.GeneralDictionaryCapturedInputCountermodel
