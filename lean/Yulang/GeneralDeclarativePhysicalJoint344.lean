import Yulang.GeneralDeclarativeOriginalReplay344

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativePhysicalJoint344
open GeneralWherePhysicalOldHead319 (before)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalPast319 (looseCtx)
open GeneralWherePhysicalCommit319 (final newChild physical_mixed_run)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalActive319 (ctx)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWhereOriginSingleSource318 (oldPlan sourceRegistry)
open GeneralWhereOriginSingleCells318 (loOld loNow hi oldChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralDeclarativePhysicalReplay344 (old_ready two_stamps three_positions)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

theorem physical_order :
    final.mixed.core.sites[1]? = some oldChild ∧ final.mixed.core.sites[2]? = some newChild ∧
    final.versionedWhere[0]? = some oldPlan ∧ final.versionedWhere[1]? = some plan := by
  rw [three_positions]
  exact ⟨rfl,rfl,two_stamps⟩

/-- Both complete replay certificates validate on the same final
assignment. The first parent's child really has nonpoint endpoints;
the current child's meanings coincide in this particular example.
The exact two stamped sites and the external output name are kept. -/
theorem both_receipts :
    ∃ prepA viewA portsA whereA rootA original intermediate prepB viewB portsB whereB rootB finalModel,
      Witness installed oldPlan original finalModel (journalSources final ++ [4]) prepA viewA portsA whereA rootA ∧
      Witness final plan intermediate finalModel ((journalSources installed ++ stateNames viewA) ++ [4])
        prepB viewB portsB whereB rootB ∧
      finalModel 4 = original 4 ∧
      ¬ Equivalent (finalModel loOld).1 (finalModel hi).1 ∧
      Equivalent (finalModel loNow).1 (finalModel hi).1 ∧
      final.mixed.core.sites[1]? = some oldChild ∧ final.mixed.core.sites[2]? = some newChild := by
  obtain ⟨stepA,_,stepB,oldModel,_,newModel,_,_⟩ := physical_mixed_run
  obtain ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,n,rawA,rawB,states⟩ :=
    GeneralDeclarativeRevalidate344.together sourceRegistry before updated looseCtx ctx oldPlan plan
      stepA stepB _ oldModel newModel old_ready GeneralWherePhysicalEvidence319.ready [4]
  have current := (GeneralDeclarativeVersionedSeparation342.mode_changes n rawB.raw).2.2.2.2
  have wrong := GeneralDeclarativeVersionedSeparation342.not_current_lower n rawB.raw
  exact ⟨prepA,viewA,portsA,whereA,rootA,_,mid,prepB,viewB,portsB,whereB,rootB,n,rawA,rawB,
    states _ List.mem_cons_self,fun same => wrong (eqv_trans same (eqv_symm current)),
    current,physical_order.1,physical_order.2.1⟩

end Yulang.GeneralDeclarativePhysicalJoint344
