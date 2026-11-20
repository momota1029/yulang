import Yulang.GeneralMixedDiagnosticReplayTrace304
import Yulang.GeneralMixedDiagnosticArchive304
import Yulang.GeneralDictionaryOutputDepthInstall252

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedDiagnosticOutputFixture304
open GeneralDictionaryOutputDepth252 (roles registry sourceRegistry root initial plan model S P F)
open GeneralDictionaryOutputDepthInstall252 (effect installed step installed_model)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralMixedDiagnosticSliceReplay304 (KeepsRequests keeps_of_outputless_rows)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects)
open CommonRoleOutermostResolver

theorem output_present : (⟨0,3⟩ : GeneralSourceState.Output) ∈ requests initial.core root := by
  apply GeneralNominalCenteredHeadOutputs.request_retained
    (GeneralNominalDemandMerging.pointSite root) (List.mem_singleton_self _) (.refl _)
  exact List.mem_singleton_self _

theorem requests_kept : KeepsRequests initial plan := by
  apply keeps_of_outputless_rows
  intro row found
  have named := GeneralNominalVersionedChildren232.emitted_occurrences plan
  rw [GeneralDictionaryOutputDepth252.children_empty] at named
  have empty : GeneralNominalVersionedChildren232.emitted plan = [] := List.map_eq_nil_iff.mp named
  unfold GeneralNominalVersionedChildren232.rawSites at found
  rw [empty] at found
  cases found

theorem real_install_with_request :
    GeneralNominalVersionedMixedKernel234.Step registry root initial installed ∧
      Models installed model ∧
      (⟨0,3⟩ : GeneralSourceState.Output) ∈ requests installed.core root :=
  ⟨step,installed_model,(requests_kept root _).mpr output_present⟩

/-- The fixture is not a request-free install and it really eliminates a
previous model. Paired semantics does not assume each side preserves models. -/
theorem strictly_refines_models :
    ∃ m, Models initial m ∧ ¬ Models installed m := by
  let small := GeneralDictionaryOutputDepthInstall252.smallModel
  refine ⟨small,GeneralDictionaryOutputDepthInstall252.small_initial,?_⟩
  intro valid
  have forced := GeneralDictionaryOutputDepthInstall252.output_forced small valid
  change CommonNominalFullCarrier.Equivalent S P at forced
  have distinct := GeneralDictionaryInspectionHeads215.tag_subtype
    (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
    (GeneralDictionaryInspectionHeads215.tagged_nominal 0
      [.inl (CommonNominalFullCarrier.nominal 0 [.inl F])]) forced.1
  cases distinct

theorem exact_install_trace :
    GeneralMixedDiagnosticReplayTrace304.Trace sourceRegistry root 1 initial installed := by
  exact .more (.zero initial) effect GeneralDictionaryOutputDepthInstall252.installable
    requests_kept .root GeneralDictionaryOutputDepthInstall252.novel

noncomputable abbrev rearchived : State roles := changeEffects installed [effect,effect]

theorem paired_archive : Correspond installed.effects [effect,effect] := by
  constructor
  · intro ex member
    have eq : ex = effect := List.mem_singleton.mp member
    subst ex
    exact ⟨effect,List.mem_cons_self,GeneralRebaseEffectSnapshot280.EffectRelated.refl _⟩
  · intro ex member
    have eq : ex = effect := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
    subst ex
    exact ⟨effect,List.mem_singleton_self _,GeneralRebaseEffectSnapshot280.EffectRelated.refl _⟩

theorem raw_distinct : rearchived ≠ installed := by
  intro eq
  have contradictionLength := congrArg (fun s : State roles => s.effects.length) eq
  change 2 = 1 at contradictionLength
  cases contradictionLength

theorem same_resolution (tree : Tree) :
    Resolves (B4TargetV8.Local (GeneralMixedDiagnosticHead304.boundary8 roles) registry installed) root tree ↔
      Resolves (B4TargetV8.Local (GeneralMixedDiagnosticHead304.boundary8 roles) registry rearchived) root tree :=
  GeneralMixedDiagnosticArchive304.same_tree paired_archive registry root tree

end Yulang.GeneralMixedDiagnosticOutputFixture304
