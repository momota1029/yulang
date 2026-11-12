import Yulang.GeneralDictionaryRecordedObservationExamples


/-! A genuine certified point replacement after a nonempty installation can
invalidate the literal current-journal invariant. Source ordinary equations
already identify endpoints 2 and 3, so replacing the queried nominal interval
(2,3) by (2,2) preserves every model. Nevertheless the newly emitted child has
syntactically different arguments from the stored child.

This obstructs unconditional transport of Current across the unrestricted
reobservation rule. It is not a counterexample to final V5 Evidence, which may
require a different readback invariant or additional journal handling. Existing
source semantics, definitions and transition rules are unchanged. -/
namespace Yulang.GeneralDictionaryCurrentRevisionObstruction
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralNominalReobservationSteps GeneralNominalCommonBridge
open CommonNominalFullCarrier

abbrev point : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (2,2)],rfl⟩
noncomputable def revision : Revision installed where
  entries := fun slot => if slot.val = 0 then some point else installed.context.state.nominals slot
  catalogue := by
    intro slot descriptor found
    split at found
    · have eq := Option.some.inj found; subst descriptor; rfl
    · exact installed.context.state.catalogue slot descriptor found
  opaqueHeads := by intro _ _ _; rfl
  domain := by
    intro slot
    by_cases one : slot.val = 0
    · have eq : slot = (0 : Fin 4) := Fin.ext one
      subst slot; change (some point = none ↔ some GeneralNominalIntervalExamples.descriptor = none); simp
    · simp [one]

noncomputable abbrev revised := revision.result

private theorem endpoints (m : Assignment)
    (ordinary : PresenceNormalForm.All CommonNominalFullCarrier.model m installed.context.state.ordinary) :
    Equivalent (m 2).1 (m 3).1 := by
  apply (GeneralNominalCaptureMerges.equations_exact m 2 (.var 3)).mp
  intro atom member
  apply ordinary atom
  simp only [installed,GeneralNominalFeedbackSites.install,Packet.privateContext,
    GeneralNominalRecursiveCandidates.privateState,GeneralNominalState.extend,
    GeneralNominalAllocation.propagate,source,List.mem_append]
  exact Or.inl (Or.inl member)

private theorem point_denotes_iff (m : Assignment)
    (equal : Equivalent (m 2).1 (m 3).1) :
    GeneralNominalState.Denotes source.base m (0 : Fin 4) point ↔
    GeneralNominalState.Denotes source.base m (0 : Fin 4) GeneralNominalIntervalExamples.descriptor := by
  constructor
  · rintro ⟨values,fits,denotes⟩
    change GeneralNominalState.FitsAll source.base m [.type (2,2)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases value with
      | inr => cases head
      | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.1⟩ .nil,denotes⟩
  · rintro ⟨values,fits,denotes⟩
    change GeneralNominalState.FitsAll source.base m [.type (2,3)] values at fits
    cases fits with
    | @cons parameter value parameters values head tail =>
      cases tail
      cases value with
      | inr => cases head
      | inl value => exact ⟨[.inl value],.cons ⟨head.1,subtype_trans head.2 equal.2⟩ .nil,denotes⟩

theorem raw_models (m : Assignment) :
    GeneralNominalState.Models revision.snapshot m ↔ GeneralNominalState.Models installed.context.state m := by
  constructor
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    by_cases one : slot.val = 0
    · have eq : slot = (0 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = GeneralNominalIntervalExamples.descriptor := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mp (valid.2.1 (0 : Fin 4) point (by rfl))
    · exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,revision,one] using found)
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    by_cases one : slot.val = 0
    · have eq : slot = (0 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = point := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mpr (valid.2.1 (0 : Fin 4) _ rfl)
    · exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,revision,one] using found)

theorem certified : Certified revision where
  raw := fun m => (raw_models m).mp
  exact := by
    intro m
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr_left (fun _ => raw_models m)


theorem improves : Improves revision := by
  constructor
  · rintro slot ⟨descriptor,found,pointed⟩
    by_cases one : slot.val = 0
    · refine ⟨point,?_,?_⟩
      · simp [Revision.snapshot,revision,one]
      · intro parameter member
        have eq := List.mem_singleton.mp member
        subst parameter; rfl
    · exact ⟨descriptor,by simpa [Revision.snapshot,revision,one] using found,pointed⟩
  · refine ⟨(0 : Fin 4),?_,point,rfl,?_⟩
    · rintro ⟨descriptor,found,pointed⟩
      have eq : descriptor = GeneralNominalIntervalExamples.descriptor := Option.some.inj found.symm
      subst descriptor
      have impossible := pointed (.type ((2 : Fin 4),(3 : Fin 4))) (List.mem_singleton_self _)
      exact (by decide +kernel : (2 : Fin 4) ≠ 3) impossible
    · intro parameter member
      have eq := List.mem_singleton.mp member
      subst parameter; rfl

theorem actual_revision : GeneralNominalReobservationSteps.Step registry root installed revised :=
  ⟨root,.root,.reobserve root revision certified improves⟩

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts GeneralDeclarationPatterns GeneralDeclarations

theorem revised_report : report revised.context declaration [((0 : Fin 4),(0 : Fin 4))] =
    captured revised.context.state (0 : Fin 4) 0 0 ((2 : Fin 4),(2 : Fin 4)) := by
  apply GeneralNominalUnaryCaptureFacts.report_exact revised.context declaration (0 : Fin 4) point rfl 0 ((2 : Fin 4),(2 : Fin 4)) rfl
  change GeneralNominalInspection.queries source context.interpretation declaration = _
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]


abbrev newChild : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles :=
  { child with demand := { child.demand with arguments := fun _ => (2,2) } }

theorem revised_children (check : DeclarationChecked registry.constructors GeneralDeclarationExamples.roles declaration) :
    GeneralNominalAllocation.children revised.context.state registry root declaration check
      (bindings revised.context.state (report revised.context declaration [((0 : Fin 4),(0 : Fin 4))])) = [newChild] := by
  rw [revised_report]
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
    normalize,child,newChild,Declaration.outputNames,bindings,captured,GeneralNominalAllocation.allocation,output]
  exact ⟨rfl,rfl,rfl⟩

theorem no_current_instance (m : Assignment) :
    ¬ GeneralDictionaryRecursiveEvidence.Instance registry revised.context m root 2 [child] := by
  rintro ⟨decl,visible,check,key,role,bounds,located,finished,ready,emitted,rest⟩
  have eq := List.mem_singleton.mp visible
  subst decl
  have found : arguments revised.context root = some [((0 : Fin 4),(0 : Fin 4))] := by rfl
  have eq := Option.some.inj (located.symm.trans found)
  subst bounds
  have emitted : [child] = [newChild] := emitted.trans (revised_children check)
  have same := List.singleton_inj.mp emitted
  have arguments := congrArg (fun c => List.ofFn c.demand.arguments) same
  exact (by decide +kernel : ([(2,3)] : List GeneralSourceState.Interval) ≠ [(2,2)]) arguments

theorem not_current : ¬ GeneralDictionaryCurrentJournal.Current registry revised := by
  intro current
  have valid := (certified.exact model).mpr installed_models
  have rule := current packet (by
    simp [revised,Revision.result,regenerate,installed,GeneralNominalFeedbackSites.install]) model valid
  apply no_current_instance model
  simpa only [children_exact,GeneralNominalDemandMerging.pointSite] using rule

theorem actual_path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root)
    initialState revised :=
  .tail (.tail .refl (GeneralNominalReobservationSteps.old_step GeneralNominalFeedbackRegressions.install_step)) actual_revision

theorem modeled_nonempty : Models revised model ∧ revised.packets ≠ [] := by
  refine ⟨(certified.exact model).mpr installed_models,?_⟩
  simp [revised,Revision.result,regenerate,installed,GeneralNominalFeedbackSites.install]

/-- The source is genuinely initial, rather than a fabricated packet list. -/
theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root :=
  GeneralNominalFeedbackObstruction.initial_source

/-- Unrestricted actual steps do not preserve this literal journal invariant. -/
theorem actual_current_failure :
    GeneralDictionaryCurrentJournal.Current registry initialState ∧
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) initialState revised ∧
    Models revised model ∧ revised.packets ≠ [] ∧
    ¬ GeneralDictionaryCurrentJournal.Current registry revised :=
  ⟨GeneralDictionaryCurrentJournal.initial_current registry context root,
    actual_path,modeled_nonempty.1,modeled_nonempty.2,not_current⟩

end Yulang.GeneralDictionaryCurrentRevisionObstruction
