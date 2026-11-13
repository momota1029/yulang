import Yulang.GeneralNominalProvenanceObserved

/-! Models of the actual first Extract installation. The two source tails
remain independent; output and repeated-capture slots retain their identities. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalProvenanceExtractModel
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource GeneralNominalProvenancePrefix
open GeneralNominalProvenanceObserved
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

noncomputable abbrev exPacket : Packet roles :=
  ⟨registry,observed.current.context,GeneralNominalFeedbackSites.childSite packet kidExtractA,extract,extract_checked,extractBounds⟩

abbrev aInputs : List Nat := [argumentLo 10 0,argumentHi 10 0,argumentLo 11 0,argumentHi 11 0,
  argumentLo 13 1,argumentHi 13 1,argumentLo 14 0,argumentHi 14 0]
abbrev bInputs : List Nat := [argumentLo 11 1,argumentHi 11 1,argumentLo 12 0,argumentHi 12 0,
  argumentLo 13 0,argumentHi 13 0,argumentLo 14 1,argumentHi 14 1]

private theorem allocated_eq (purpose owner position purpose' owner' position' : Nat)
    (same : allocated purpose owner position = allocated purpose' owner' position') :
    purpose = purpose' ∧ owner = owner' ∧ position = position' := by
  have equal := (GeneralNominalAllocation.source_identity state registry root.identity _ _).mp same
  exact ⟨congrArg (fun key => key.2.2.1) equal,congrArg (fun key => key.2.2.2.1) equal,
    congrArg (fun key => key.2.2.2.2) equal⟩

private theorem a_b_disjoint (identity : Nat) (one : identity ∈ aInputs) : identity ∉ bInputs := by
  intro two
  simp only [aInputs,bInputs,List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases two with same | same | same | same | same | same | same | same
  all_goals have equal := allocated_eq _ _ _ _ _ _ same
  all_goals omega

private theorem allocated_large (purpose owner position : Nat) : 7 < allocated purpose owner position :=
  GeneralNominalIdentities.source_above_seed _ _

noncomputable def modelFor (a b u : Ty) : GeneralNominalCommonBridge.Assignment := fun identity =>
  if identity ≤ 7 then GeneralNominalProvenanceSource.model a b u identity else
    if identity ∈ aInputs then (nominal 0 [.inl a],Common.rowEmpty) else
    if identity ∈ bInputs then (nominal 0 [.inl b],Common.rowEmpty) else (a,Common.rowEmpty)

variable (a b u : Ty)
local notation "assignment" => modelFor a b u

theorem source_small (identity : Nat) (small : identity ≤ 7) :
    assignment identity = GeneralNominalProvenanceSource.model a b u identity := by simp [modelFor,small]

theorem a_input (identity : Nat) (member : identity ∈ aInputs) :
    (assignment identity).1 = nominal 0 [.inl a] := by
  have large : 7 < identity := by
    simp only [aInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact allocated_large _ _ _
  simp [modelFor,show ¬identity ≤ 7 by omega,member]
  rfl

theorem b_input (identity : Nat) (member : identity ∈ bInputs) :
    (assignment identity).1 = nominal 0 [.inl b] := by
  have large : 7 < identity := by
    simp only [bInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact allocated_large _ _ _
  have absent : identity ∉ aInputs := fun one => a_b_disjoint identity one member
  simp [modelFor,show ¬identity ≤ 7 by omega,member,absent]
  rfl

theorem output_value (name : Nat) : (assignment (output name)).1 = a := by
  have absentA : output name ∉ aInputs := by
    intro member
    simp only [aInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same
    all_goals have equal := allocated_eq _ _ _ _ _ _ same
    all_goals omega
  have absentB : output name ∉ bInputs := by
    intro member
    simp only [bInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same
    all_goals have equal := allocated_eq _ _ _ _ _ _ same
    all_goals omega
  have large := allocated_large 2 name 0
  simp [modelFor,show ¬ output name ≤ 7 by exact Nat.not_le.mpr large,absentA,absentB]
  rfl

theorem source_models : GeneralNominalState.Models state assignment := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro _ _ impossible; cases impossible
  · intro _ member; cases member
  · intro slot descriptor recorded
    change entries slot = some descriptor at recorded
    unfold entries at recorded
    split at recorded
    · rename_i same; subst slot; cases Option.some.inj recorded
      apply (GeneralNominalState.denotes_singleton_exact base _ 0 1 (listDescriptor 1) rfl).mpr
      exact ⟨subtype_refl _,subtype_refl _⟩
    · split at recorded
      · rename_i same; subst slot; cases Option.some.inj recorded
        apply (GeneralNominalState.denotes_singleton_exact base _ 1 2 (listDescriptor 2) rfl).mpr
        exact ⟨subtype_refl _,subtype_refl _⟩
      · split at recorded
        · rename_i same; subst slot; cases Option.some.inj recorded
          apply (GeneralNominalState.denotes_singleton_exact base _ 3 4 (listDescriptor 4) rfl).mpr
          exact ⟨subtype_refl _,subtype_refl _⟩
        · split at recorded
          · rename_i same; subst slot; cases Option.some.inj recorded
            apply (GeneralNominalState.denotes_singleton_exact base _ 4 5 (listDescriptor 5) rfl).mpr
            exact ⟨subtype_refl _,subtype_refl _⟩
          · split at recorded
            · rename_i same; subst slot; cases Option.some.inj recorded
              apply (GeneralNominalState.denotes_singleton_exact base _ 6 7 boxDescriptor rfl).mpr
              exact ⟨subtype_refl _,subtype_refl _⟩
            · cases recorded

private theorem fixed {ref : GeneralNominalProjections.Ref} {value actual : Ty}
    (one : Observes assignment (embed ref) value) (two : Observes assignment (embed ref) actual) : Equivalent actual value :=
  nominal_observation_unique assignment ref actual value two one
private theorem seen_outer_zero : Observes assignment (outer 0) (nominal 0 [.inl a]) :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_outer_three : Observes assignment (outer 3) (nominal 0 [.inl b]) :=
  .nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_inner_zero : Observes assignment (inner 0) a :=
  .nominal (seen_outer_zero a b u) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem seen_inner_three : Observes assignment (inner 3) b :=
  .nominal (seen_outer_three a b u) ⟨subtype_refl _,subtype_refl _⟩ rfl
private theorem outer_zero (actual : Ty) (seen : Observes assignment (outer 0) actual) : Equivalent actual (nominal 0 [.inl a]) :=
  fixed a b u (ref := .argument (.source 0) 0 0) (seen_outer_zero a b u) seen
private theorem outer_three (actual : Ty) (seen : Observes assignment (outer 3) actual) : Equivalent actual (nominal 0 [.inl b]) :=
  fixed a b u (ref := .argument (.source 3) 0 0) (seen_outer_three a b u) seen
private theorem inner_zero (actual : Ty) (seen : Observes assignment (inner 0) actual) : Equivalent actual a :=
  fixed a b u (ref := .argument (.argument (.source 0) 0 0) 0 0) (seen_inner_zero a b u) seen
private theorem inner_three (actual : Ty) (seen : Observes assignment (inner 3) actual) : Equivalent actual b :=
  fixed a b u (ref := .argument (.argument (.source 3) 0 0) 0 0) (seen_inner_three a b u) seen

private theorem parent_projection : ProjectionModels state reportP assignment := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨⟨_,seen_outer_zero a b u⟩,fun actual seen => ⟨(outer_zero a b u actual seen).2,(outer_zero a b u actual seen).1⟩⟩
    · exact ⟨⟨_,seen_inner_zero a b u⟩,fun actual seen => ⟨(inner_zero a b u actual seen).2,(inner_zero a b u actual seen).1⟩⟩
    · exact ⟨⟨_,seen_outer_three a b u⟩,fun actual seen => ⟨(outer_three a b u actual seen).2,(outer_three a b u actual seen).1⟩⟩
    · exact ⟨⟨_,seen_inner_three a b u⟩,fun actual seen => ⟨(inner_three a b u actual seen).2,(inner_three a b u actual seen).1⟩⟩
  · intro test member actual seen
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨[.inl a],rfl,outer_zero a b u actual seen⟩
    · exact ⟨[.inl b],rfl,outer_three a b u actual seen⟩
  · intro first one last two same origin recorded actual seen
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals cases same
    all_goals cases recorded
    all_goals first
      | exact ⟨(inner_zero a b u actual seen).2,(inner_zero a b u actual seen).1⟩
      | exact ⟨(inner_three a b u actual seen).2,(inner_three a b u actual seen).1⟩
  · intro first one last two same x y ha hb v z hv hz
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
    all_goals cases same
    all_goals cases ha
    all_goals cases hb
    · exact nominal_observation_unique assignment (.argument (.argument (.source 0) 0 0) 0 0) v z hv hz
    · exact nominal_observation_unique assignment (.argument (.argument (.source 3) 0 0) 0 0) v z hv hz

private def binderValue (a b : Ty) (name : Nat) : Ty := if name = 1 then b else a
private theorem use_shapes (entry : GeneralNominalMaterialization.Use) (member : entry ∈ schema.variables) :
    (∃ identity, identity ∈ aInputs ∧ entry = inputUse identity 0) ∨
    (∃ identity, identity ∈ bInputs ∧ entry = inputUse identity 1) ∨ entry = outputUse 3 ∨ entry = outputUse 4 := by
  simp only [schema,inputUses,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr rfl))
    | exact Or.inl ⟨_,by simp [aInputs],rfl⟩
    | exact Or.inr (Or.inl ⟨_,by simp [bInputs],rfl⟩)

private theorem use_value (entry : GeneralNominalMaterialization.Use) (member : entry ∈ schema.variables) :
    (∃ actual, Observes assignment entry.origin actual) ∧
      ∀ actual, Observes assignment entry.origin actual → Equivalent actual (binderValue a b entry.name) := by
  rcases use_shapes entry member with ⟨identity,present,rfl⟩ | ⟨identity,present,rfl⟩ | rfl | rfl
  · have seen : Observes assignment (inputUse identity 0).origin a := by
      apply Observes.nominal (.source _)
      · rw [a_input a b u identity present]; exact ⟨subtype_refl _,subtype_refl _⟩
      · rfl
    exact ⟨⟨_,seen⟩,fun actual observed => fixed a b u (ref := .argument (.source identity) 0 0) seen observed⟩
  · have seen : Observes assignment (inputUse identity 1).origin b := by
      apply Observes.nominal (.source _)
      · rw [b_input a b u identity present]; exact ⟨subtype_refl _,subtype_refl _⟩
      · rfl
    exact ⟨⟨_,seen⟩,fun actual observed => fixed a b u (ref := .argument (.source identity) 0 0) seen observed⟩
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    change Equivalent (assignment (output 3)).1 a
    rw [output_value a b u 3]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    change Equivalent (assignment (output 4)).1 a
    rw [output_value a b u 4]
    exact ⟨subtype_refl _,subtype_refl _⟩

private theorem parent_material : GeneralNominalMaterialization.Models state p
    (GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings)
    reportP schema assignment := by
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have shape : (∃ identity, identity ∈ aInputs ∧ test = (.source identity,.nominal 0 1)) ∨
        (∃ identity, identity ∈ bInputs ∧ test = (.source identity,.nominal 0 1)) := by
      simp only [schema,inputTests,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (apply Or.inl; refine ⟨_,?_,rfl⟩; simp [aInputs]; done)
        | (apply Or.inr; refine ⟨_,?_,rfl⟩; simp [bInputs]; done)
    rcases shape with ⟨identity,present,rfl⟩ | ⟨identity,present,rfl⟩
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      rw [a_input a b u identity present]
      exact ⟨[.inl a],rfl,subtype_refl _,subtype_refl _⟩
    · refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      rw [b_input a b u identity present]
      exact ⟨[.inl b],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    refine ⟨(use_value a b u entry member).1,?_⟩
    intro actual seen
    have equal := (use_value a b u entry member).2 actual seen
    rcases use_shapes entry member with ⟨identity,present,rfl⟩ | ⟨identity,present,rfl⟩ | rfl | rfl
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 0) actual
      rw [packet_bindings]
      exact ⟨equal.2,equal.1⟩
    · change GeneralNominalCaptureMerges.Fits assignment
        ((GeneralNominalAllocation.capture state registry root.identity p.id packet.bindings).inputs 1) actual
      rw [packet_bindings]
      exact ⟨equal.2,equal.1⟩
    · change Equivalent actual (assignment (output 3)).1
      rw [output_value a b u 3]
      exact equal
    · change Equivalent actual (assignment (output 4)).1
      rw [output_value a b u 4]
      exact equal
  · intro first one last two same _ _ v z hv hz
    have left := (use_value a b u first one).2 v hv
    have right := (use_value a b u last two).2 z hz
    rw [same] at left
    exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
  · intro entry member captured present same _ origin recorded v z hv hz
    have left := (use_value a b u entry member).2 v hv
    rw [same] at left
    simp only [reportP,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl
    all_goals cases recorded
    · have right := inner_zero a b u z hz
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · have right := inner_three a b u z hz
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩

theorem parent_models : packet.Holds assignment := by
  refine ⟨?_,?_,?_⟩
  · change GeneralNominalState.Models (privateState registry context root p pBounds) assignment
    unfold privateState
    rw [p_bindings,report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨source_models a b u,?_,?_⟩
      · intro first one last two same
        simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
        rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
        all_goals cases same
        all_goals exact subtype_refl _
      · simp [GeneralNominalAllocation.merges,Declaration.inputNames,p,normalizeArgs,normalize,
          variablesArgs,Pattern.variables,GeneralNominalAllocation.occurrences,PresenceNormalForm.All]
    · intro atom member
      simp only [selfChecks,reportP,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact subtype_refl _
  · change ProjectionModels state (report context p pBounds) assignment
    rw [report_exact]
    exact parent_projection a b u
  · change GeneralNominalMaterialization.Models state p _ (report context p pBounds)
      (generated registry context root p p_checked pBounds) assignment
    rw [report_exact,schema_exact]
    simpa only [Packet.bindings,report_exact,GeneralNominalDemandMerging.pointSite] using parent_material a b u

theorem observed_models : Models observed.current assignment := by
  apply (GeneralNominalProvenanceObserved.observed_models assignment).mpr
  apply (GeneralNominalFeedbackSites.install_models start.current packet _ rfl assignment).mpr
  exact ⟨(GeneralNominalSaturationState.initial_models ..).mpr (source_models a b u),parent_models a b u⟩


noncomputable abbrev merged (purpose : Nat) := GeneralNominalAllocation.source observed.current.context.state
  registry kidExtractA.identity (GeneralNominalAllocation.origin kidExtractA.identity extract.id purpose 0 0)

theorem extract_bindings : exPacket.bindings = [(0,(2,2)),(0,(2,2))] := by
  unfold Packet.bindings
  rw [extract_report]
  rfl

theorem merged_value (purpose : Nat) : (assignment (merged purpose)).1 = a := by
  have rootLess : root.identity < kidExtractA.identity :=
    GeneralNominalIdentities.source_above_invocation state.seed
      (GeneralNominalAllocation.origin root.identity p.id 6 extractA.id 0)
  have distinct : ∀ oldPurpose owner position, merged purpose ≠ allocated oldPurpose owner position := by
    intro oldPurpose owner position same
    have equal := (GeneralNominalIdentities.source_identity state.seed _ _).mp same
    have invocation := congrArg Prod.fst equal
    change kidExtractA.identity = root.identity at invocation
    omega
  have absentA : merged purpose ∉ aInputs := by
    intro member
    simp only [aInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same
    all_goals exact distinct _ _ _ same
  have absentB : merged purpose ∉ bInputs := by
    intro member
    simp only [bInputs,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same
    all_goals exact distinct _ _ _ same
  have large : 7 < merged purpose := GeneralNominalIdentities.source_above_seed state.seed _
  simp [modelFor,show ¬merged purpose ≤ 7 by omega,absentA,absentB]
  rfl

private theorem inputOrigin (identity : Nat) (member : identity ∈ aInputs) :
    (∃ actual, Observes assignment (.nominal (.source identity) 0 0) actual) ∧
      ∀ actual, Observes assignment (.nominal (.source identity) 0 0) actual → Equivalent actual a := by
  have recorded : Observes assignment (.nominal (.source identity) 0 0) a := by
    apply Observes.nominal (.source _)
    · rw [a_input a b u identity member]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · rfl
  exact ⟨⟨_,recorded⟩,fun actual seen => nominal_observation_unique assignment (.argument (.source identity) 0 0) actual a seen recorded⟩

private theorem actualOrigin (origin : Origin)
    (which : origin = .nominal (.source (argumentLo 10 0)) 0 0 ∨
      origin = .nominal (.source (argumentHi 10 0)) 0 0) :
    (∃ actual, Observes assignment origin actual) ∧ ∀ actual, Observes assignment origin actual → Equivalent actual a := by
  rcases which with rfl | rfl
  · exact inputOrigin a b u _ (by simp [aInputs])
  · exact inputOrigin a b u _ (by simp [aInputs])

private theorem extract_projection : ProjectionModels observed.current.context.state extractReport assignment := by
  have low := actualOrigin a b u _ (Or.inl rfl)
  have high := actualOrigin a b u _ (Or.inr rfl)
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    simp only [extractReport,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨low.1,fun actual seen => ⟨(low.2 actual seen).2,(low.2 actual seen).1⟩⟩
    · exact ⟨high.1,fun actual seen => ⟨(high.2 actual seen).2,(high.2 actual seen).1⟩⟩
  · intro test member; cases member
  · intro first one last two same origin recorded actual seen
    simp only [extractReport,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl
    all_goals cases recorded
    all_goals first
      | exact ⟨(low.2 actual seen).2,(low.2 actual seen).1⟩
      | exact ⟨(high.2 actual seen).2,(high.2 actual seen).1⟩
  · intro first one last two same x y hx hy v z hv hz
    simp only [extractReport,List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl
    all_goals cases hx
    all_goals cases hy
    all_goals first
      | exact ⟨subtype_trans (low.2 v hv).1 (low.2 z hz).2,subtype_trans (low.2 z hz).1 (low.2 v hv).2⟩
      | exact ⟨subtype_trans (low.2 v hv).1 (high.2 z hz).2,subtype_trans (high.2 z hz).1 (low.2 v hv).2⟩
      | exact ⟨subtype_trans (high.2 v hv).1 (low.2 z hz).2,subtype_trans (low.2 z hz).1 (high.2 v hv).2⟩
      | exact ⟨subtype_trans (high.2 v hv).1 (high.2 z hz).2,subtype_trans (high.2 z hz).1 (high.2 v hv).2⟩

theorem extract_schema : GeneralNominalPacketSupport.namedSchema exPacket =
    ⟨[⟨0,.source (output 3),.actual⟩],[],false⟩ := by
  change generated registry observed.current.context kidExtractA extract extract_checked extractBounds = _
  have request : kidExtractA.demand.outputs = [⟨1,output 3⟩] := rfl
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration extract = extract := by
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      extract,List.mergeSort_nil]
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  simp [request,GeneralNominalMaterialization.rootRequests,extract,
    GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralDeclarationDemands.emitAll,normalize]

private theorem extract_material : GeneralNominalPacketSupport.Outputs exPacket assignment := by
  unfold GeneralNominalPacketSupport.Outputs GeneralNominalPacketSupport.report
  rw [extract_schema,extract_report]
  have captured : ((GeneralNominalPacketSupport.capture exPacket).inputs 0) = (merged 0,merged 1) := by
    unfold GeneralNominalPacketSupport.capture
    rw [extract_bindings]
    rfl
  refine ⟨(by intro test member; cases member),?_,?_,?_⟩
  · intro entry member
    have same := List.mem_singleton.mp member; subst entry
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual seen; cases seen
    change GeneralNominalCaptureMerges.Fits assignment ((GeneralNominalPacketSupport.capture exPacket).inputs 0)
      (assignment (output 3)).1
    rw [captured]
    unfold GeneralNominalCaptureMerges.Fits
    rw [merged_value a b u 0,merged_value a b u 1,output_value a b u 3]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _ _ _ v z hv hz
    have same := List.mem_singleton.mp one; subst first
    have same := List.mem_singleton.mp two; subst last
    cases hv; cases hz
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member capture present _ _ origin recorded v z hv hz
    have same := List.mem_singleton.mp member; subst entry
    cases hv
    simp only [extractReport,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    all_goals cases recorded
    all_goals rw [output_value a b u 3]
    · exact ⟨(actualOrigin a b u _ (Or.inl rfl)).2 z hz |>.2,(actualOrigin a b u _ (Or.inl rfl)).2 z hz |>.1⟩
    · exact ⟨(actualOrigin a b u _ (Or.inr rfl)).2 z hz |>.2,(actualOrigin a b u _ (Or.inr rfl)).2 z hz |>.1⟩

theorem extract_models : exPacket.Holds assignment := by
  refine ⟨?_,?_,extract_material a b u⟩
  · change GeneralNominalState.Models (privateState registry observed.current.context kidExtractA extract extractBounds) assignment
    unfold GeneralNominalRecursiveCandidates.privateState
    rw [extract_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨(observed_models a b u).1,?_,?_⟩
      · intro first one last two _
        change first ∈ [(0,(2,2)),(0,(2,2))] at one
        change last ∈ [(0,(2,2)),(0,(2,2))] at two
        simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at one two
        subst first; subst last
        exact subtype_refl _
      · change PresenceNormalForm.All CommonNominalFullCarrier.model assignment
          (GeneralNominalAllocation.equations (merged 0) (.union (.var 2) (.var 2)) ++
            GeneralNominalAllocation.equations (merged 1) (.inter (.var 2) (.var 2)))
        apply (PresenceNormalForm.all_append ..).mpr
        constructor
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          change Equivalent (assignment (merged 0)).1 (.union a a)
          rw [merged_value a b u 0]
          exact ⟨(common_union_is_join a a (.union a a)).mp (subtype_refl _) |>.1,
            (common_union_is_join a a a).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
        · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
          change Equivalent (assignment (merged 1)).1 (.inter a a)
          rw [merged_value a b u 1]
          exact ⟨(common_inter_is_meet a a a).mpr ⟨subtype_refl _,subtype_refl _⟩,
            (common_inter_is_meet a a (.inter a a)).mp (subtype_refl _) |>.1⟩
    · intro atom member
      simp only [selfChecks,extractReport,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals first
        | exact subtype_refl _
        | change Subtype (assignment (argumentLo 10 0)).1 (assignment (argumentHi 10 0)).1
          rw [a_input a b u _ (by simp [aInputs]),a_input a b u _ (by simp [aInputs])]
          exact subtype_refl _
  · rw [extract_report]
    exact extract_projection a b u

theorem combined_models : Models observed.current assignment ∧ exPacket.Holds assignment :=
  ⟨observed_models a b u,extract_models a b u⟩

end Yulang.GeneralNominalProvenanceExtractModel
