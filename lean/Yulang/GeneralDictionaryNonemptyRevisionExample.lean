import Yulang.GeneralDictionaryRecordedObservationExamples
import Yulang.GeneralDictionaryKeyedRevision

/-! A nonempty installed journal followed by genuine replacement at an unused
nominal slot. The root's queried descriptor and report remain unchanged. The
parent Instance is retained; no Evidence for its rejected child is claimed. -/
namespace Yulang.GeneralDictionaryNonemptyRevisionExample
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralNominalReobservationSteps GeneralNominalCommonBridge
open CommonNominalFullCarrier

abbrev point : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (2,2)],rfl⟩
noncomputable def revision : Revision installed where
  entries := fun slot => if slot.val = 1 then some point else installed.context.state.nominals slot
  catalogue := by
    intro slot descriptor found
    split at found
    · have eq := Option.some.inj found; subst descriptor; rfl
    · exact installed.context.state.catalogue slot descriptor found
  opaqueHeads := by intro _ _ _; rfl
  domain := by
    intro slot
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
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
    GeneralNominalState.Denotes source.base m (1 : Fin 4) point ↔
    GeneralNominalState.Denotes source.base m (1 : Fin 4) GeneralNominalIntervalExamples.descriptor := by
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
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = GeneralNominalIntervalExamples.descriptor := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mp (valid.2.1 (1 : Fin 4) point (by rfl))
    · exact valid.2.1 slot descriptor (by simpa [Revision.snapshot,revision,one] using found)
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    by_cases one : slot.val = 1
    · have eq : slot = (1 : Fin 4) := Fin.ext one
      subst slot
      have eq : descriptor = point := Option.some.inj found.symm
      subst descriptor
      exact (point_denotes_iff m (endpoints m valid.2.2)).mpr (valid.2.1 (1 : Fin 4) _ rfl)
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
    by_cases one : slot.val = 1
    · refine ⟨point,?_,?_⟩
      · simp [Revision.snapshot,revision,one]
      · intro parameter member
        have eq := List.mem_singleton.mp member
        subst parameter; rfl
    · exact ⟨descriptor,by simpa [Revision.snapshot,revision,one] using found,pointed⟩
  · refine ⟨(1 : Fin 4),?_,point,rfl,?_⟩
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

theorem reports : GeneralDictionaryRecordedRevisionTrace.Reports registry installed revision := by
  intro stored member
  have eq : stored = packet := by
    simpa only [installed,GeneralNominalFeedbackSites.install,initialState,initial,
      List.mem_cons,List.not_mem_nil,or_false] using member
  subst stored
  intro decl visible _ bounds located
  have eq := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  apply GeneralDictionaryInspectionTransport.nominal_unary_report installed.context
    (GeneralDictionaryRecordedRevisionTrace.observation installed revision)
    declaration (0 : Fin 4) GeneralNominalIntervalExamples.descriptor rfl rfl 0
    ((2 : Fin 4),(3 : Fin 4)) rfl
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate]
  rfl

theorem actual_path : B4Target.Steps (GeneralDictionaryRecordedRevisionTrace.Step registry root)
    initialState revised := by
  apply B4Target.Steps.tail (t := installed)
  · exact .tail .refl (.feedback (.ordinary ⟨GeneralNominalFeedbackRegressions.install_step,
      GeneralDictionaryOrdinaryTrace.install_extension initialState packet rfl⟩))
  · exact .revision installed revision reports certified actual_revision

theorem nonempty_current : revised.packets ≠ [] ∧ GeneralDictionaryCurrentJournal.Current registry revised := by
  refine ⟨?_,GeneralDictionaryRecordedRevisionTrace.initial_trace_current registry root context revised actual_path⟩
  simp [revised,Revision.result,regenerate,installed,GeneralNominalFeedbackSites.install]

theorem modeled_parent : Models revised model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry revised.context model root 2 [child] := by
  have valid := (certified.exact model).mpr installed_models
  have rule := nonempty_current.2 packet (by
    simp [revised,Revision.result,regenerate,installed,GeneralNominalFeedbackSites.install]) model valid
  refine ⟨valid,?_⟩
  simpa only [children_exact,GeneralNominalDemandMerging.pointSite] using rule

theorem changed_existing_descriptor :
    installed.context.state.nominals (1 : Fin 4) = some GeneralNominalIntervalExamples.descriptor ∧
    revised.context.state.nominals (1 : Fin 4) = some point ∧
    GeneralNominalIntervalExamples.descriptor ≠ point := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have args := congrArg GeneralNominalState.Descriptor.arguments same
  exact (by decide +kernel : GeneralNominalIntervalExamples.descriptor.arguments ≠ point.arguments) args


set_option backward.isDefEq.respectTransparency false in
theorem recorded_footprint : GeneralDictionaryKeyedRevision.RecordedFootprint registry installed revision := by
  intro stored member
  have eq : stored = packet := by
    simpa only [installed,GeneralNominalFeedbackSites.install,initialState,initial,
      List.mem_cons,List.not_mem_nil,or_false] using member
  subst stored
  intro decl visible _ _ bounds located slot read
  have eq := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  have query : GeneralNominalInspection.queries installed.context.state installed.context.interpretation declaration =
      [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate]
    rfl
  rw [query] at read
  have fp : GeneralDictionaryInspectionLocality.footprints installed.context.state
      [.nominal 0 [.variables [0]]] [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] = [⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩] := by
    decide +kernel
  rw [fp] at read
  have zero : slot = (0 : Fin 4) := by simpa using read
  subst slot
  rfl

theorem keyed_path : B4Target.Steps (GeneralDictionaryKeyedRevision.Step registry root)
    initialState revised := by
  apply B4Target.Steps.tail (t := installed)
  · exact .tail .refl (.ordinary ⟨GeneralNominalFeedbackRegressions.install_step,
      GeneralDictionaryOrdinaryTrace.install_extension initialState packet rfl⟩)
  · exact GeneralDictionaryKeyedRevision.footprint_step registry root installed revision recorded_footprint certified actual_revision

end Yulang.GeneralDictionaryNonemptyRevisionExample
