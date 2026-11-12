import Yulang.GeneralNominalRecursiveRegressions

/-! A concrete inspected parameter with lower int and upper top. The endpoints
have distinct identities and meanings. Scalar matching does not wait for the
upper head, and a different known lower constructor eliminates the candidate. -/
namespace Yulang.GeneralNominalNonpointInspectionExamples

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralSourceState (equationAtoms equationAtoms_exact)
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors)

abbrev base : GeneralSourceState.State where
  slots := 4
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 2 (.base .int) ++ equationAtoms 3 .top
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 2 then .scalar .int else .unresolved
  intervals := []
  heads_sound := by
    intro assignment models slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 4)) = term := by
        simpa [GeneralSourceState.Head.equation] using recorded
      subst term
      exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp models).1
    · simp [two,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 2 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 4)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head rfl
    · simp [two,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (2,3)],rfl⟩
abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; rfl
    · simp [zero] at recorded

abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then nominal 0 [.inl (.base .int)]
    else if identity = 2 then .base .int else .top,Common.rowEmpty)

theorem int_top : Subtype (.base .int) .top :=
  (CommonNominalFullModelMap.subtype_exact _ _).mpr (CommonBoundCoalescing.le_top (.base .int))

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    change atom ∈ equationAtoms (2 : Fin 4) (.base .int) ++ equationAtoms 3 .top at member
    simp only [equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | (rfl | rfl) <;> exact subtype_refl _
  · intro slot scalar recorded
    by_cases two : slot = 2
    · subst slot
      have same : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 4)) = scalar := by
        simpa [GeneralSourceState.Head.equation] using recorded
      subst scalar; exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [two,GeneralSourceState.Head.equation] at recorded
  · intro slot impossible; cases impossible
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      have same := Option.some.inj recorded; subst d
      exact ⟨[.inl (.base .int)],.cons ⟨subtype_refl _,int_top⟩ .nil,subtype_refl _,subtype_refl _⟩
    · simp [zero] at recorded

abbrev intDecl := GeneralNominalRegressions.concreteList
abbrev strDecl : Declaration := ⟨5,0,[.app 0 [.app 3 []]],[],[],[]⟩
abbrev intRegistry := GeneralNominalRegressions.concreteRegistry
abbrev strRegistry : Registry := ⟨constructors,roles,[strDecl]⟩
abbrev interpretation : GeneralNominalInspection.Interpretation where
  primitives := fun key => if key = 2 then some (.scalar .int) else if key = 3 then some (.scalar .str) else none
  invariantNominal := fun key => key == 0
  disjoint := by intro key nominal; have zero : key = 0 := by simpa using nominal
                 subst key; rfl
abbrev context : Context := ⟨state,interpretation⟩
abbrev root := GeneralNominalExamples.displayRoot
abbrev parameterOrigin := Origin.nominal (.source 0) 0 0
abbrev calculated : Report state where
  inspected := [(0,0),(2,3)]
  checked := [(0,0),(0,0),(2,3)]
  anchors := [(parameterOrigin,(2,3))]
  tests := [(parameterOrigin,.scalar .int)]

theorem endpoints_different : (2 : Fin 4) ≠ 3 ∧ (model 2).1 ≠ (model 3).1 :=
  ⟨by decide +kernel,by intro impossible; cases impossible⟩

theorem int_report : report context intDecl [(0,0)] = calculated := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,inspectMany,inspect,typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.visit,Report.append]

theorem str_conflicts : (report context strDecl [(0,0)]).conflicts = [(2,3)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,inspectMany,inspect,typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.visit,Report.append]

theorem projected_int (actual : Ty) (seen : Observes model parameterOrigin actual) : Equivalent actual (.base .int) :=
  nominal_observation_unique model (.argument (.source 0) 0 0) actual (.base .int) seen
    (.nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl)

theorem projection_models : ProjectionModels state calculated model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    have same := List.mem_singleton.mp member; subst anchor
    refine ⟨⟨.base .int,.nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl⟩,?_⟩
    intro actual seen
    exact ⟨(projected_int actual seen).2,subtype_trans (projected_int actual seen).1 int_top⟩
  · intro test member actual seen
    have same := List.mem_singleton.mp member; subst test
    exact projected_int actual seen
  · intro _ impossible; cases impossible
  · intro _ impossible; cases impossible

theorem int_schema : generated intRegistry context root intDecl GeneralNominalRegressions.concrete_checked [(0,0)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem int_survivor : Survivor intRegistry context root 4 [] := by
  have located : arguments context root = some [(0,0)] := by decide +kernel
  refine ⟨?_,intDecl,by simp,GeneralNominalRegressions.concrete_checked,rfl,rfl,[(0,0)],located,?_,?_⟩
  · rintro ⟨index,unknown⟩; exact unknown ⟨0,rfl,Or.inr ⟨descriptor,rfl⟩⟩
  · refine ⟨?_,?_,GeneralNominalUnaryCaptureFacts.initial_fresh _ _ _ (by decide +kernel),[(0,0)],located,?_,?_,model,?_,?_,?_⟩
    · refine ⟨rfl,?_⟩
      intro key primitive recorded
      by_cases two : key = 2
      · subst key
        have same := Option.some.inj recorded; subst primitive
        exact ⟨⟨[],2⟩,rfl,rfl⟩
      · by_cases three : key = 3
        · subst key
          have same : GeneralCandidateInspection.Primitive.scalar .str = primitive := by simpa using recorded
          subst primitive
          exact ⟨⟨[],3⟩,rfl,rfl⟩
        · simp [two,three] at recorded
    · exact ⟨fun _ => ⟨by simp [GeneralNominalState.sources,List.ofFn_succ],by simp [GeneralNominalState.sources,List.ofFn_succ]⟩,
        by intro _ impossible; cases impossible⟩
    · rw [int_report]; exact ⟨rfl,rfl,rfl⟩
    · exact ⟨(by intro _ impossible; cases impossible),(by rw [int_schema])⟩
    · unfold privateState
      rw [int_report]
      apply (GeneralNominalState.extend_models ..).mpr
      constructor
      · apply (GeneralNominalAllocation.propagate_models ..).mpr
        exact ⟨state_models,(by intro _ impossible; cases impossible),PresenceNormalForm.all_nil _ _⟩
      · intro atom member
        simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl
        · exact subtype_refl _
        · exact subtype_refl _
        · exact int_top
    · rw [int_report]; exact projection_models
    · rw [int_schema]; exact GeneralNominalMaterialization.empty_models ..
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
    rfl

theorem no_str_survivors (key : Nat) (children : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ Survivor strRegistry context root key children := by
  rintro ⟨_,declaration,visible,_,_,_,_,_,prepared,_⟩
  have same := List.mem_singleton.mp visible; subst declaration
  obtain ⟨_,_,_,bounds,located,finished,_⟩ := prepared
  have found : arguments context root = some [(0,0)] := by decide +kernel
  have same := Option.some.inj (found.symm.trans located); subst bounds
  have conflict : (report context strDecl [(0,0)]).conflicts = [] := finished.2.1
  rw [str_conflicts] at conflict
  cases conflict

theorem str_checked : DeclarationChecked constructors roles strDecl := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,GeneralDeclarationExamples.constructors]
  all_goals intro clause member; cases member

theorem str_finished_inspection :
    (report context strDecl [(0,0)]).blocked = [] ∧ (report context strDecl [(0,0)]).arity = [] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,inspectMany,inspect,typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.visit,Report.append]

theorem str_failed : Failed strRegistry context root strDecl str_checked := by
  refine ⟨?_,GeneralNominalUnaryCaptureFacts.initial_fresh _ _ _ (by decide +kernel),[(0,0)],
    by decide +kernel,str_finished_inspection.1,str_finished_inspection.2,Or.inl ?_⟩
  · obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := int_survivor
    exact prepared.1
  · rw [str_conflicts]; simp

theorem str_not_pending : ¬ InspectionPending strRegistry context root := by
  rintro ⟨_,declaration,visible,checked,_,notFailed,_⟩
  have same := List.mem_singleton.mp visible; subst declaration
  exact notFailed str_failed

theorem str_rejected : GeneralNominalLocalBoundary.Local
    (GeneralNominalLocalBoundary.recursiveFields roles) strRegistry context root .rejected :=
  .rejected ⟨int_survivor.1,Or.inr (Or.inr ⟨str_not_pending,no_str_survivors⟩)⟩

end Yulang.GeneralNominalNonpointInspectionExamples
