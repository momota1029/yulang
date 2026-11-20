import Yulang.GeneralMixedDiagnosticLocal304
import Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralMixedDiagnosticSliceCounterexample304
open GeneralNominalVersionedJournal232 (State Models lift)
open GeneralNominalVersionedMergedConflict232 (HistoryModels MergedOutputConflict)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralNominalCenteredHeadAllocMergeSource (roles)
open GeneralNominalCenteredHeadAllocMergeState (stage)
open GeneralNominalCenteredHeadAllocV7MergeRegression (focus conflict_stage)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype observeTy model)

abbrev impossibleAtom : PresenceNormalForm.Atom Nat := .tyLe .top .bottom

theorem impossible_atom (m : Assignment) : ¬ impossibleAtom.Holds model m := by
  intro sat
  change Subtype .top .bottom at sat
  let environment : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row :=
    ⟨fun _ => .bottom,fun _ => []⟩
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (sat 0)
    0 environment .impossible (by simp [observeTy,CommonNominalSyntax.Layer.evalAt])
  simp [observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
    CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at impossible

abbrev first : State roles := lift (stage [impossibleAtom])

/-- Keep all current fields intact; change only the stored source context.
The comparison below concerns arbitrary states, not common-source reachability. -/
def last : State roles :=
  let old := first.core.erased.source
  let falseSource := { old with state := GeneralNominalState.extend old.state [] [impossibleAtom] }
  { first with legacy := { first.legacy with core := {
    first.core with erased := { first.core.erased with source := falseSource } } } }

theorem no_first_models (m : Assignment) : ¬ Models first m := by
  intro good
  exact impossible_atom m (good.1.1.2.2 impossibleAtom (List.mem_singleton_self _))

theorem no_last_models (m : Assignment) : ¬ Models last m := by
  intro good
  exact impossible_atom m (good.1.1.2.2 impossibleAtom (List.mem_singleton_self _))

theorem same_head : HeadView first last :=
  ⟨⟨rfl,rfl,rfl,fun m => ⟨fun h => False.elim (no_first_models m h),
    fun h => False.elim (no_last_models m h)⟩⟩,rfl,rfl⟩

theorem first_conflict : MergedOutputConflict first focus :=
  (GeneralNominalVersionedMergedConflict232.conflict_lift (stage [impossibleAtom]) focus).mpr conflict_stage

theorem no_last_history (m : Assignment) : ¬ HistoryModels last m := by
  intro h
  have atoms := h.1.1.2.2
  exact impossible_atom m (atoms impossibleAtom (List.mem_append_right _ (List.mem_singleton_self _)))

theorem last_clear : ¬ MergedOutputConflict last focus := by
  intro conflict
  obtain ⟨m,valid⟩ := GeneralNominalVersionedMergedConflict232.conflict_inhabited conflict
  exact no_last_history m valid

theorem head_view_alone_insufficient :
    HeadView first last ∧ MergedOutputConflict first focus ∧ ¬ MergedOutputConflict last focus :=
  ⟨same_head,first_conflict,last_clear⟩

end Yulang.GeneralMixedDiagnosticSliceCounterexample304
