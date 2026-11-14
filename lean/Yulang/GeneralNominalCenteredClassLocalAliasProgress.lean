import Yulang.GeneralNominalCenteredCompletionAliasObstruction
import Yulang.GeneralNominalCenteredModelExtension

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! The earlier merged snapshot still enables equality feedback at the plain
focus. This is concrete progress, not a claim about its eventual local result. -/
namespace Yulang.GeneralNominalCenteredClassLocalAliasProgress
open GeneralNominalCenteredCompletionAliasSource GeneralNominalCenteredCompletionAliasTrace
open GeneralNominalCenteredCompletionAliasLocal
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalExamples (state context listDescriptor state_models)

theorem output_above_one : 1 < output := GeneralNominalIdentities.source_above_seed (state true).seed _

def variantModel : GeneralNominalCommonBridge.Assignment := fun name =>
  if name = output then (nominal 0 [.inl (.base .int)],Common.rowEmpty) else exampleModel name

theorem variant_source : GeneralNominalState.Models (state true) variantModel := by
  apply GeneralNominalCenteredModelExtension.source_models_same (state true) (first := exampleModel) _ (state_models true)
  intro name member
  have small : name ≤ 1 := source.below_seed name member
  have different : name ≠ output := by have above := output_above_one; omega
  simp [variantModel,different]

theorem variant_context : GeneralNominalState.Models current.state variantModel := by
  have model := GeneralNominalUnaryCaptureFacts.private_models (context true) registry root parent 0 listDescriptor rfl 0 rfl (1,1) rfl query variantModel variant_source
  apply (GeneralNominalState.extend_models ..).mpr
  exact ⟨model.1,by intro atom member; cases member⟩

theorem output_member : output ∈ GeneralNominalState.sources current.state := by
  have reserved : output ∈ GeneralNominalAllocation.reserved (state true) registry root.identity := by
    apply List.mem_map.mpr
    exact ⟨(100,1,5,30,0),by decide +kernel,rfl⟩
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_append_left _ reserved)))

theorem one_member : 1 ∈ GeneralNominalState.sources current.state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩))))

theorem equal : GeneralNominalFeedbackK2.Equal finish.erased.current output 1 := by
  intro m valid
  have one := valid.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  have out := output_int m valid
  exact ⟨subtype_trans out.1 one.2,subtype_trans one.1 out.2⟩

theorem not_raw_equal : ¬ GeneralNominalFeedbackSteps.RawEqual finish.erased.current output 1 := by
  intro same
  have compared := same variantModel variant_context
  have different : (1 : Nat) ≠ output := by have above := output_above_one; omega
  have impossible : Subtype (.base .int) (nominal 0 [.inl (.base .int)]) := by
    simpa [variantModel,different,GeneralNominalExamples.model] using compared.2
  exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 _ impossible

noncomputable abbrev equated := administrative finish (GeneralNominalFeedbackSteps.equate finish.erased.current output 1)

theorem equate_at : At registry finish focus equated :=
  .administrative focus _ (.equate focus output 1 output_member one_member equal not_raw_equal)

theorem equate_step : Step registry root finish equated :=
  ⟨focus,GeneralNominalCenteredCompletionAliasObstruction.generated_focus,equate_at⟩

theorem not_stable : ¬ Stable registry finish focus :=
  fun stable => stable focus .root equated equate_at

theorem no_committed_frame (candidate : Plan roles)
    (frame : GeneralNominalCenteredSelectedCompletion.Frame registry finish focus 2 descendants candidate) :
    ¬ GeneralNominalFeedbackSteps.Committed finish.erased.current candidate.packet := by
  intro committed
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil descendants descendants_nonempty
  have edge := committed.2 child (frame.children_eq ▸ member)
  rw [frame.occurrence_eq] at edge
  change (focus,child) ∈ [] ++ children.map (fun c => (root,c)) at edge
  have edge' : (focus,child) ∈ children.map (fun c => (root,c)) := by simpa only [List.nil_append] using edge
  obtain ⟨_,_,same⟩ := List.mem_map.mp edge'
  have identity := congrArg (fun pair => pair.1.identity) same
  have above := GeneralNominalIdentities.source_above_invocation (state true).seed (100,1,6,11,0)
  change root.identity < focus.identity at above
  exact (Nat.ne_of_lt above) identity

theorem stable_extension : ∃ final,
    B4Target.Steps (Step registry root) finish final ∧ Stable registry final root ∧ Stable registry final focus := by
  let final := GeneralNominalCenteredGroundComposition.terminalState registry finish root
  have checked : (GeneralNominalCenteredAdministrativeLocal.boundary roles).Checked registry := ⟨rfl,registry_checked⟩
  have path : B4Target.Steps (Step registry root) finish final :=
    GeneralNominalCenteredAdministrativeComposition.execution registry checked finish root ground_reachable
  have reachable := B4TargetV5.reachable_steps _ ground_reachable path
  have halted := GeneralNominalCenteredAdministrativeComposition.halted registry checked finish root ground_reachable
  have closed := GeneralNominalCenteredAdministrativeComposition.closure registry checked final root reachable halted
  have grows : ∀ {last}, B4Target.Steps (Step registry root) finish last →
      GeneralNominalSaturationState.Generated last.erased.current root focus := by
    intro last trace
    induction trace with
    | refl => exact GeneralNominalCenteredCompletionAliasObstruction.generated_focus
    | tail path step ih =>
      obtain ⟨_,_,action⟩ := step
      exact GeneralNominalSaturationSteps.generated_monotone (GeneralNominalCenteredTrace.at_extends action).journal ih
  exact ⟨final,path,closed.1,closed.2 focus (grows path)⟩

end Yulang.GeneralNominalCenteredClassLocalAliasProgress
