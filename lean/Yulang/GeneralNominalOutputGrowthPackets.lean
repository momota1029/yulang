import Yulang.GeneralNominalOutputGrowthModels

/-! Actual candidate capture, named materialization, and feedback installation
for the output-growth declaration. Each finite input prefix has a selected
candidate and a real installation; this does not assert an infinite Step trace. -/
namespace Yulang.GeneralNominalOutputGrowthPackets

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalOutputGrowth GeneralNominalOutputGrowthModels
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralNominalSaturationState CommonNominalFullCarrier

abbrev slot (length : Nat) : Fin (source length).base.slots := ⟨length,by change length < length+2; omega⟩
abbrev endpoint (length : Nat) : Fin (source length).base.slots := ⟨length+1,by change length+1 < length+2; omega⟩
abbrev bounds (length : Nat) := [(slot length,slot length)]
abbrev packet (length : Nat) : Packet roles :=
  ⟨registry,context length,GeneralNominalDemandMerging.pointSite (root length),declaration,declaration_checked,bounds length⟩
abbrev output (length : Nat) := GeneralNominalAllocation.source (source length) registry (root length).identity
  (GeneralNominalAllocation.origin (root length).identity 2 2 1 0)
abbrev child (length : Nat) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (source length) registry (root length).identity
    (GeneralNominalAllocation.origin (root length).identity 2 6 20 0),
    ⟨1,fun _ => (length+1,length+1),[⟨0,output length⟩],by
      intro o member; have same := List.mem_singleton.mp member; subst o; exact ⟨none,rfl⟩⟩⟩

private theorem query (length : Nat) : GeneralNominalInspection.queries (source length)
    (context length).interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,source]

theorem report_exact (length : Nat) : report (context length) declaration (bounds length) =
    captured (source length) (slot length) 0 0 (endpoint length,endpoint length) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context length) declaration (slot length)
    (descriptor length (slot length) (Nat.le_refl _)) (dite_eq_left (Nat.le_refl _)) 0
    (endpoint length,endpoint length) rfl (query length)

theorem bindings_exact (length : Nat) : (packet length).bindings = [(0,(length+1,length+1))] := by
  unfold Packet.bindings
  rw [report_exact]
  rfl

theorem children_exact (length : Nat) : (packet length).children = [child length] := by
  unfold Packet.children
  rw [bindings_exact]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,Declaration.outputNames,GeneralNominalAllocation.allocation,output]
  repeat constructor <;> rfl

theorem schema_exact (length : Nat) : generated registry (context length) (root length) declaration declaration_checked (bounds length) =
    ⟨[⟨1,.nominal (.source (length+1)) 0 0,.actual⟩,⟨1,.source (output length),.actual⟩],
      [(.source (length+1),.nominal 0 1)],false⟩ := by
  unfold generated
  rw [report_exact]
  unfold GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,Declaration.outputNames,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,normalize,normalizeArgs,bindings,captured,
    output,GeneralNominalAllocation.allocation,source]

theorem output_fresh (length : Nat) : length+1 < output length :=
  GeneralNominalIdentities.source_above_seed _ _

private theorem schema_models (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (equation : Equivalent (model (length+1)).1 (nominal 0 [.inl (model (output length)).1])) :
    GeneralNominalMaterialization.Models (source length) declaration
      (GeneralNominalAllocation.capture (source length) registry (root length).identity declaration.id (packet length).bindings)
      (report (context length) declaration (bounds length))
      (generated registry (context length) (root length) declaration declaration_checked (bounds length)) model := by
  rw [schema_exact,report_exact,bindings_exact]
  have observed : Observes model (.nominal (.source (length+1)) 0 0) (model (output length)).1 :=
    .nominal (.source _) equation rfl
  have unique : ∀ actual, Observes model (.nominal (.source (length+1)) 0 0) actual →
      Equivalent actual (model (output length)).1 := fun actual seen =>
    nominal_observation_unique model (.argument (.source (length+1)) 0 0) actual _ seen observed
  have all : ∀ use ∈ [({name := 1,origin := .nominal (.source (length+1)) 0 0,mode := .actual} : GeneralNominalMaterialization.Use),
      ⟨1,.source (output length),.actual⟩], ∀ actual, Observes model use.origin actual → Equivalent actual (model (output length)).1 := by
    intro use member actual seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact unique actual seen
    · cases seen; exact ⟨subtype_refl _,subtype_refl _⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    exact ⟨[.inl (model (output length)).1],rfl,equation⟩
  · intro use member
    have result := all use member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨_,observed⟩,fun actual seen => unique actual seen⟩
    · exact ⟨⟨_,.source _⟩,fun actual seen => by cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro first one last two _ _ _ a b ha hb
    exact ⟨subtype_trans (all first one a ha).1 (all last two b hb).2,
      subtype_trans (all last two b hb).1 (all first one a ha).2⟩
  · intro use member c present same _
    have equal := List.mem_singleton.mp present; subst c
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> cases same

theorem packet_models (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (validPrefix : PrefixModels length model)
    (equation : Equivalent (model (length+1)).1 (nominal 0 [.inl (model (output length)).1])) :
    (packet length).Holds model := by
  have original := GeneralNominalUnaryCaptureFacts.private_models (context length) registry (root length)
    declaration (slot length) (descriptor length (slot length) (Nat.le_refl _))
    (dite_eq_left (Nat.le_refl _)) 0 rfl (endpoint length,endpoint length) rfl (query length)
    model ((source_models length model).mpr validPrefix)
  exact ⟨original.1,original.2,schema_models length model equation⟩

theorem finite_packet_models (length : Nat) : (packet length).Holds (finiteModel (length+1)) := by
  apply packet_models length _ (prefix_refines length _ (finite_prefix_models (length+1)))
  have depth : length+1+1-output length = 0 := by have fresh := output_fresh length; omega
  change Equivalent (tower (length+1+1-(length+1))) (nominal 0 [.inl (tower (length+1+1-output length))])
  rw [depth]
  have one : length+1+1-(length+1) = 1 := by omega
  rw [one]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem regular_packet_models (length : Nat) : (packet length).Holds GeneralNominalProgressObstruction.model :=
  packet_models length _ (regular_prefix_models length) GeneralNominalProgressObstruction.equation

theorem located (length : Nat) : arguments (context length) (root length) = some (bounds length) := by
  have slotFound := (GeneralDictionaryBinderLocations.sourceSlot_exact (base length) length (slot length)).mpr rfl
  change GeneralCandidateBoundaryParts.locate (base length) [(length,length)] = _
  simp [GeneralCandidateBoundaryParts.locate,slotFound,bounds,Option.bind]
  rfl

theorem prepared (length : Nat) : Prepared registry (context length) (root length) declaration declaration_checked := by
  refine ⟨metadata length,linked length,GeneralNominalSourceFormation.initial_fresh _ (initial_source length) _,
    bounds length,located length,?_,?_,_,finite_packet_models length⟩
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member; subst output
      exact ⟨⟨22,0,.app 0 [.var 1]⟩,by simp,rfl⟩
    · rw [schema_exact]

theorem survivor (length : Nat) : Survivor registry (context length) (root length) 2 (packet length).children :=
  ⟨ready length,declaration,by simp,declaration_checked,rfl,rfl,bounds length,located length,prepared length,rfl⟩

private theorem legacy_clear (length : Nat) (slot : Fin (source length).base.slots) :
    ¬ GeneralNominalMixedRecurrence.RecursAt (source length) slot := by
  rintro ⟨⟨kind,_,_⟩,_⟩; exact Fin.elim0 kind

theorem selected (length : Nat) : GeneralNominalFeedbackK2.Local registry (snapshot length) (root length)
    (.selected 2 (packet length).children) := by
  refine .selected ⟨ready length,not_rootK2 length,not_candidateK2 length,?_⟩ ⟨survivor length,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,_,_,_,missing⟩ := pending
      have same := List.mem_singleton.mp visible; subst d
      exact missing (prepared length)
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · exact legacy_clear length slot cycle
      · exact legacy_clear length visited.1 cycle
  · intro key children found
    have copy := found
    obtain ⟨_,d,visible,_,identity,_⟩ := found
    have same := List.mem_singleton.mp visible; subst d
    have same : key = 2 := identity.symm; subst key
    exact ⟨rfl,survivor_children_functional registry checked (context length) (root length) 2 _ _ copy (survivor length)⟩

theorem enabled (length : Nat) : GeneralNominalFeedbackSteps.Installable registry (snapshot length) (packet length) := by
  refine ⟨?_,selected length,?_⟩
  · refine ⟨rfl,rfl,by simp [snapshot,initial],by simp,rfl,located length,prepared length,
      GeneralNominalFeedbackK2.selected_legacy (selected length),?_,?_,?_,?_⟩
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member; subst other; exact .refl _
    · exact ⟨finiteModel (length+1),(snapshot_models length _).mpr
        (prefix_refines length _ (finite_prefix_models (length+1))),finite_packet_models length⟩
    · exact GeneralNominalJointCandidates.initial_joint registry (context length) (root length) declaration
        (by simp) declaration_checked rfl (bounds length) (located length) (prepared length) _ (finite_packet_models length)
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _

noncomputable def installed (length : Nat) := GeneralNominalFeedbackSites.install (snapshot length) (packet length)
  (GeneralNominalFeedbackSites.emitted (packet length))

theorem install_step (length : Nat) : GeneralNominalFeedbackSteps.Step registry (root length)
    (snapshot length) (installed length) := by
  refine ⟨root length,.root,.install (packet length) (enabled length) ?_⟩
  intro committed
  have absent := committed.2 (child length) (by rw [children_exact]; simp)
  cases absent

theorem installed_formed (length : Nat) : GeneralNominalFeedbackSteps.SourceFormed registry (root length) (installed length) :=
  .update (formed length) (install_step length)

theorem installed_models (length : Nat) : Models (installed length) (finiteModel (length+1)) := by
  apply (GeneralNominalFeedbackSites.install_models (snapshot length) (packet length) _ rfl _).mpr
  exact ⟨(snapshot_models length _).mpr (prefix_refines length _ (finite_prefix_models (length+1))),finite_packet_models length⟩

theorem installed_acyclic (length identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle (installed length) identity :=
  feedback_acyclic (installed length) _ (installed_models length) (fun i => length+1+1-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

theorem child_pending (length : Nat) :
    GeneralNominalState.RootPending (source length) (child length).demand := by
  refine ⟨⟨0,by exact Nat.zero_lt_succ 0⟩,?_⟩
  rintro ⟨s,equal,head | nominal⟩
  · exact head rfl
  · obtain ⟨d,recorded⟩ := nominal
    have identity : s.val = length+1 := equal
    change (if bound : s.val ≤ length then some (descriptor length s bound) else none) = some d at recorded
    rw [dite_eq_right (by omega)] at recorded
    cases recorded

theorem fixed_snapshot_whereAccessible (length : Nat) :
    Acc (CommonRoleOutermostResolver.Child (GeneralNominalFeedbackK2.Local registry (snapshot length))) (root length) := by
  refine Acc.intro (root length) ?_
  rintro next ⟨key,children,localRule,member⟩
  have same := GeneralNominalFeedbackK2.local_functional localRule (selected length)
  cases same
  rw [children_exact] at member
  have equal := List.mem_singleton.mp member; subst next
  refine Acc.intro (child length) ?_
  rintro next ⟨key,children,localRule,member⟩
  cases localRule with
  | selected safe _ => exact False.elim (safe.1 (child_pending length))

theorem regular_installed_models (length : Nat) : Models (installed length) GeneralNominalProgressObstruction.model := by
  apply (GeneralNominalFeedbackSites.install_models (snapshot length) (packet length) _ rfl _).mpr
  exact ⟨(snapshot_models length _).mpr (regular_prefix_models length),regular_packet_models length⟩

/-- This obstruction uses an actual enabled installation and its actual emitted
child, with a model of the complete installed journal. -/
theorem no_modelwise_child_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Ty → Measure) (length : Nat) :
    ¬ (∀ model, Models (installed length) model →
      less (rank (model ((child length).demand.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩).1).1)
        (rank (model ((root length).demand.arguments ⟨0,by exact Nat.zero_lt_succ 0⟩).1).1)) := by
  intro decreases
  have self := decreases GeneralNominalProgressObstruction.model (regular_installed_models length)
  have irreflexive : ∀ value, ¬ less value value := by
    intro value
    induction wellFounded.apply value with
    | intro value below ih => intro loop; exact ih value loop loop
  exact irreflexive _ self

theorem packet_output_equation (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (valid : (packet length).Holds model) :
    Equivalent (model (length+1)).1 (nominal 0 [.inl (model (output length)).1]) := by
  have material := valid.2.2
  change GeneralNominalMaterialization.Models (source length) declaration _ _
    (generated registry (context length) (root length) declaration declaration_checked (bounds length)) model at material
  rw [schema_exact] at material
  obtain ⟨arguments,size,equal⟩ := (material.1 (.source (length+1),.nominal 0 1) (by simp)).2 _ (.source _)
  have projected := material.2.1 ⟨1,.nominal (.source (length+1)) 0 0,.actual⟩ (by simp)
  cases arguments with
  | nil => cases size
  | cons argument rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
    subst rest
    cases argument with
    | inl value =>
      have captured := projected.2 value (.nominal (.source _) equal rfl)
      change GeneralNominalMaterialization.VariableHolds declaration
        (GeneralNominalAllocation.capture (source length) registry (root length).identity declaration.id
          (packet length).bindings) model 1 .actual value at captured
      rw [bindings_exact] at captured
      change Equivalent value (model (output length)).1 at captured
      have congruence := GeneralNominalState.singleton_nominal_congr 0 _ _ captured
      exact ⟨subtype_trans equal.1 congruence.1,subtype_trans congruence.2 equal.2⟩
    | inr row =>
      obtain ⟨actual,seen⟩ := projected.1
      cases seen with
      | nominal parent compared found =>
        cases parent
        have incompatible := ((nominal_regular_invariant_exact _ _ _ _).mp
          (subtype_trans equal.2 compared.1)).2.2 0 (.inr row) (.inl actual) rfl found
        exact False.elim incompatible

end Yulang.GeneralNominalOutputGrowthPackets
