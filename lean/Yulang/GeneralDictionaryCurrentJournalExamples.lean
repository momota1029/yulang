import Yulang.GeneralDictionaryCurrentJournal

/-! A real installation and descriptor-changing refresh exercise the journal
invariant. The final context is NOT an ordinary Extension of the original packet
context; its generated child's nominal descriptor changed. No complete parent
dictionary is asserted, since that child is rejected by K2. -/
namespace Yulang.GeneralDictionaryCurrentJournalExamples
open GeneralNominalFeedbackObstruction GeneralNominalFeedbackRefresh
open GeneralNominalSaturationState GeneralDictionaryCurrentJournal
open GeneralDictionaryFinishedTrace

theorem actual_path : B4Target.Steps (Step registry root) initialState refreshed := by
  exact .tail (.tail .refl (.ordinary ⟨GeneralNominalFeedbackRegressions.install_step,
    GeneralDictionaryOrdinaryTrace.install_extension initialState packet rfl⟩))
    Actual.descriptor_changing_step

theorem recorded : packet ∈ refreshed.packets := by
  simp [refreshed,regenerate,installed,GeneralNominalFeedbackSites.install]

theorem current_parent (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshed.context m root 2 [child] := by
  have rule := initial_trace_current registry root context refreshed actual_path packet recorded m valid
  change GeneralDictionaryRecursiveEvidence.Instance registry refreshed.context m root 2 packet.children at rule
  rw [children_exact] at rule
  exact rule

theorem no_original_extension :
    ¬ GeneralDictionaryOrdinaryTrace.Extension packet.context refreshed.context := by
  rintro ⟨reserved,atoms,allocated,equal⟩
  have impossible := congrArg (fun (c : GeneralNominalCandidates.Context) =>
    ((List.ofFn c.state.nominals).map (Option.map (fun d => d.constructor)))[2]?) equal
  change (some (some 0) : Option (Option Nat)) = some none at impossible
  cases impossible

theorem nonvacuous_beyond_extension :
    Models refreshed model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry refreshed.context model root 2 [child] ∧
    ¬ GeneralDictionaryOrdinaryTrace.Extension packet.context refreshed.context := by
  have valid := (refresh_models model).mpr installed_models
  exact ⟨valid,current_parent model valid,no_original_extension⟩

/-- Any further actual restricted trace retains this recorded parent in its
new current context; no old packet-to-final Extension premise is added. -/
theorem arbitrary_tail (after : State GeneralDeclarationExamples.roles)
    (tail : B4Target.Steps (Step registry root) refreshed after)
    (m : GeneralNominalCommonBridge.Assignment) (valid : Models after m) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context m root 2 [child] := by
  have previous := GeneralNominalFeedbackSteps.steps_models
    (trace_feedback registry root refreshed after tail) m valid
  exact trace_instance registry root root refreshed after tail m valid 2 [child]
    (current_parent m previous)

end Yulang.GeneralDictionaryCurrentJournalExamples
