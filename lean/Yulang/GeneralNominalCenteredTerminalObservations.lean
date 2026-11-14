import Yulang.GeneralNominalCenteredTerminalForkSource
set_option backward.isDefEq.respectTransparency false

/-! Actual terminal revisions of one ground source preserve all models and
recorded packets, but disagree on an unregistered observer's literal children.
The stronger all-demand observation agreement does not follow from this
semantic closure. This does not refute the priority-aware final Local law. -/
namespace Yulang.GeneralNominalCenteredTerminalObservations
open GeneralNominalCenteredTerminalForkSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

abbrev model := GeneralNominalExamples.model

theorem source_model (choice : Option Bool) : GeneralNominalState.Models (snapshot choice) model := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    simp only [base,GeneralSourceState.equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | (rfl | rfl) <;> exact subtype_refl _
  · intro slot term recorded
    by_cases zero : slot = 0
    · simp [base,zero,GeneralSourceState.Head.equation] at recorded
    · have equal : (.base .int : Core.PresenceGeneration.TyTerm (Fin 3)) = term := by
        simpa [base,zero,GeneralSourceState.Head.equation] using recorded
      subst term
      have nonzero : slot.val ≠ 0 := fun h => zero (Fin.ext h)
      change Equivalent (if slot.val = 0 then _ else _) (.base .int)
      rw [ite_eq_right nonzero]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro interval member; cases member
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : descriptor choice = d := Option.some.inj recorded
      subst d
      refine ⟨[.inl (.base .int)],?_,subtype_refl _,subtype_refl _⟩
      cases choice with
      | none => exact .cons ⟨subtype_refl _,subtype_refl _⟩ .nil
      | some side => cases side <;> exact .cons ⟨subtype_refl _,subtype_refl _⟩ .nil
    · simp [snapshot,zero] at recorded
  · exact PresenceNormalForm.all_nil _ _

theorem inhabited (side : Bool) : ∃ model, GeneralNominalCenteredSteps.Models (finish side) model :=
  ⟨model,(finish_models side model).mpr (source_model (some side))⟩

abbrev target (side : Bool) : Nat := if side then 2 else 1
abbrev child (side : Bool) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (snapshot (some side)) registry observer.identity
      (GeneralNominalAllocation.origin observer.identity display.id 6 10 0),
    ⟨0,fun _ => (target side,target side),[],by intro _ member; cases member⟩⟩

theorem query (side : Bool) : GeneralNominalInspection.queries (snapshot (some side))
    GeneralNominalExamples.interpretation display = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_exact (side : Bool) : report (context (some side)) display [(0,0)] =
    GeneralNominalUnaryCaptureFacts.captured (snapshot (some side)) 0 0 0 (bounds (some side)) :=
  GeneralNominalUnaryCaptureFacts.report_exact (context (some side)) display 0 (descriptor (some side))
    rfl 0 (bounds (some side)) rfl (query side)

theorem children_exact (side : Bool) : GeneralNominalAllocation.children (snapshot (some side)) registry observer
    display display_checked [(0,(target side,target side))] = [child side] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,normalize,child]

theorem survivor (side : Bool) : Survivor registry (context (some side)) observer 1 [child side] := by
  have located : arguments (context (some side)) observer = some [(0,0)] := by
    change arguments (context none) observer = some [(0,0)]
    decide +kernel
  have privateModels := GeneralNominalUnaryCaptureFacts.private_models (context (some side)) registry observer
    display 0 (descriptor (some side)) rfl 0 rfl (bounds (some side)) rfl (query side) model (source_model (some side))
  have schema := GeneralNominalRecursiveExamples.display_schema registry (context (some side)) observer rfl display_checked [(0,0)]
  refine ⟨?_,display,List.mem_singleton_self _,display_checked,rfl,rfl,[(0,0)],located,?_,?_⟩
  · rintro ⟨index,unknown⟩
    exact unknown ⟨0,rfl,Or.inr ⟨descriptor (some side),rfl⟩⟩
  · refine ⟨metadata _,?_,GeneralNominalSourceFormation.initial_fresh _ (source (some side)) observer.identity,
      [(0,0)],located,?_,⟨?_,?_⟩,model,privateModels.1,privateModels.2,?_⟩
    · constructor
      · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
      · intro output member; cases member
    · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
    · intro output member; cases member
    · rw [schema]
    · rw [schema]; exact GeneralNominalMaterialization.empty_models ..
  · rw [report_exact]
    have bindings : bindings (snapshot (some side))
        (GeneralNominalUnaryCaptureFacts.captured (snapshot (some side)) 0 0 0 (bounds (some side))) =
        [(0,(target side,target side))] := by cases side <;> rfl
    rw [bindings]
    exact (children_exact side).symm

theorem children_different : [child false] ≠ [child true] := by
  intro equal
  have childEq : child false = child true := List.singleton_inj.mp equal
  have endpoints := congrArg (fun d : Occurrence roles =>
    List.ofFn (fun index => (d.demand.arguments index).1)) childEq
  change [1] = [2] at endpoints
  contradiction

theorem child_identity_same : (child false).identity = (child true).identity := rfl

theorem child_inputs_equivalent (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredSteps.Models (finish false) model) :
    Equivalent (model ((child false).demand.arguments ⟨0,by decide +kernel⟩).1).1
      (model ((child true).demand.arguments ⟨0,by decide +kernel⟩).1).1 := by
  have source := (finish_models false model).mp valid
  have first := scalar model source 1 (by decide +kernel)
  have last := scalar model source 2 (by decide +kernel)
  exact ⟨subtype_trans first.1 last.2,subtype_trans last.1 first.2⟩

theorem observations_different :
    ¬ GeneralNominalCenteredAdministrativeComposition.ObservationAgreement registry (finish false) (finish true) := by
  intro same
  have carried : Survivor registry (context (some true)) observer 1 [child false] :=
    (same.survivor observer 1 [child false]).mp (survivor false)
  exact children_different (survivor_children_functional registry registry_checked _ observer 1 _ _ carried (survivor true))

theorem same_committed (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalFeedbackSteps.Committed (finish false).erased.current packet ↔
      GeneralNominalFeedbackSteps.Committed (finish true).erased.current packet := by
  have raw (model : GeneralNominalCommonBridge.Assignment) :
      GeneralNominalSaturationState.Models (finish false).erased.current model ↔
        GeneralNominalSaturationState.Models (finish true).erased.current model :=
    (GeneralNominalSaturationState.initial_models (context (some false)) root model).trans
      ((models_iff (some false) (some true) model).trans
        (GeneralNominalSaturationState.initial_models (context (some true)) root model).symm)
  constructor
  · intro committed
    exact ⟨fun model valid => committed.1 model ((raw model).mpr valid),committed.2⟩
  · intro committed
    exact ⟨fun model valid => committed.1 model ((raw model).mp valid),committed.2⟩

theorem observer_unregistered (side : Bool) :
    ¬ GeneralNominalCenteredAdministrativeLocal.Registered (finish side) observer := by
  rintro ⟨site,member,same⟩
  have exactSite := List.mem_singleton.mp member
  subst site
  have identity := congrArg Occurrence.identity same
  change 700 = 100 at identity
  contradiction

theorem observer_not_selected (side : Bool) (key : Nat) (children : List (Occurrence roles)) :
    ¬ GeneralNominalCenteredAdministrativeLocal.Local registry (finish side) observer (.selected key children) :=
  fun selected => observer_unregistered side (GeneralNominalCenteredAdministrativeLocal.selected_ready selected).1

theorem committed_semantics_do_not_determine_observations :
    (∀ packet, GeneralNominalFeedbackSteps.Committed (finish false).erased.current packet ↔
      GeneralNominalFeedbackSteps.Committed (finish true).erased.current packet) ∧
    ¬ GeneralNominalCenteredAdministrativeComposition.ObservationAgreement registry (finish false) (finish true) :=
  ⟨same_committed,observations_different⟩

theorem terminal_observation_fork :
    GeneralNominalSourceFormation.InitialSource registry (context none) root ∧
    GeneralNominalGroundAccessibility.GroundRoots (context none) root [.app 2 []] ∧
    (∀ side, GeneralNominalCenteredSteps.Step registry root start (finish side)) ∧
    (∀ side next, ¬ GeneralNominalCenteredSteps.Step registry root (finish side) next) ∧
    (∀ side, ∃ model, GeneralNominalCenteredSteps.Models (finish side) model) ∧
    (∀ model, GeneralNominalCenteredSteps.Models (finish false) model ↔ GeneralNominalCenteredSteps.Models (finish true) model) ∧
    (finish false).erased.current.packets = (finish true).erased.current.packets ∧
    ¬ GeneralNominalCenteredAdministrativeComposition.ObservationAgreement registry (finish false) (finish true) :=
  ⟨source none,ground,step,halted,inhabited,same_models,rfl,observations_different⟩

end Yulang.GeneralNominalCenteredTerminalObservations
