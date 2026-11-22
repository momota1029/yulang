import Yulang.GeneralDeclarativeTwoViews344
import Yulang.GeneralDeclarativeVersionedSeparation342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativePhysicalReplay344
open GeneralWherePhysicalOldHead319 (before start)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalPast319 (looseCtx)
open GeneralWherePhysicalCommit319 (final newChild physical_mixed_run)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalActive319 (ctx)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWhereOriginSingleSource318 (oldPlan sourceRegistry)
open GeneralWhereOriginSingleCells318 (loOld loNow hi oldChild)
open GeneralWhereVersionInstall317 (Models emitted)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDeclarativeTwoViews344 (together)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativeLedger344 (Grows)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Equation)
open GeneralWhereOriginSupport318 (journalSources)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

theorem old_ready : Ready installed.mixed.core root oldPlan := by
  intro out current
  apply GeneralWherePhysicalOldPick319.ready out
  exact (GeneralWhereOriginSuccessor318.requests_unchanged start.core looseCtx oldPlan
    GeneralWherePhysicalOldInstall319.silent root out).mp current

theorem middle_prefix : Grows installed updated := by
  exact ⟨⟨[],by rfl⟩,⟨[],by
    change updated.mixed.core.sites = installed.mixed.core.sites ++ []
    rw [List.append_nil]
    rfl⟩⟩

theorem old_stamp : installed.versionedWhere[0]? = some oldPlan := rfl

theorem two_stamps :
    final.versionedWhere[0]? = some oldPlan ∧ final.versionedWhere[1]? = some plan := by
  refine ⟨GeneralDeclarativeLedger344.stamped
    (GeneralDeclarativeLedger344.trans middle_prefix (GeneralDeclarativeLedger344.step GeneralWherePhysicalCommit319.step)) old_stamp,?_⟩
  rw [GeneralWherePhysicalCommit319.both_in_history]
  rfl

theorem three_positions :
    final.mixed.core.sites =
      [GeneralWherePhysicalCurrentPick319.sourceRoot,oldChild,newChild] := by
  change updated.mixed.core.sites ++ emitted plan = _
  rw [GeneralWherePhysicalCurrentPick319.centers,GeneralWherePhysicalCommit319.emission]
  rfl

/-- The first genuine version has semantically nonpoint child
endpoints. The second changes only the lower endpoint address, and
both independent ordinary replays are true on one protected model.
The archived child stays at its original position, never becomes the
selected current child merely because its occurrence ID is shared. -/
theorem phases :
    ∃ prepA viewA portsA whereA rootA baseModel mid prepB viewB portsB whereB rootB n,
      Witness installed oldPlan baseModel mid (journalSources final ++ [4]) prepA viewA portsA whereA rootA ∧
      Witness final plan mid n ((journalSources installed ++ GeneralDeclarativeFootprint321.stateNames viewA) ++ [4])
        prepB viewB portsB whereB rootB ∧
      Models installed n ∧ Models final n ∧
      GeneralDeclarativeHead320.Models viewA n ∧ GeneralDeclarativeHead320.Models viewB n ∧
      n 4 = baseModel 4 ∧
      ¬ Equivalent (n loOld).1 (n hi).1 ∧
      Equivalent (n loNow).1 (n hi).1 := by
  obtain ⟨stepA,_,stepB,oldModel,_,newModel,_,_⟩ := physical_mixed_run
  obtain ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,n,
    rawA,rawB,typedOld,typedNew,okA,okB,stable⟩ :=
    together sourceRegistry before updated looseCtx ctx oldPlan plan stepA stepB _ oldModel newModel
      old_ready GeneralWherePhysicalEvidence319.ready [4]
  have current := (GeneralDeclarativeVersionedSeparation342.mode_changes n typedNew).2.2.2.2
  have apart := GeneralDeclarativeVersionedSeparation342.not_current_lower n typedNew
  refine ⟨prepA,viewA,portsA,whereA,rootA,_,mid,prepB,viewB,portsB,whereB,rootB,n,
    rawA,rawB,typedOld,typedNew,okA,okB,stable _ List.mem_cons_self,?_,current⟩
  intro wrong
  exact apart (eqv_trans wrong (GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm current))

end Yulang.GeneralDeclarativePhysicalReplay344
