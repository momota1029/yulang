import Yulang.GeneralVersionedForwardedJoint312
import Yulang.GeneralVersionedAliasChoice312
import Yulang.GeneralLatePeerJoint311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 7000000
namespace Yulang.Cycle312ActualProbe
open GeneralLatePeerSource311 (registry checked parentCode route)
open GeneralLatePeerMerge311 (final reached)
open GeneralVersionedForwardedWrites312 (Forwarded)

theorem root_forwarded : Forwarded parentCode := by
  simp [Forwarded,GeneralDeclarations.Declaration.outputNames,GeneralNominalCenteredHeadAllocEncoding.declaration,
    GeneralNominalCenteredHeadAllocEncoding.clause,GeneralLatePeerSource311.atLeft,
    GeneralLatePeerSource311.atRoute]
  decide +kernel

theorem route_forwarded : Forwarded route := by
  simp [Forwarded,GeneralDeclarations.Declaration.outputNames,
    GeneralLatePeerSource311.makePeer]

theorem current_raw (m : GeneralNominalCommonBridge.Assignment)
    (model : GeneralNominalVersionedJournal232.Models final m) :
    (GeneralNominalPacketSupport.report GeneralLatePeerFinalPeerPlan311.packet).conflicts = [] ∧
    GeneralVersionedProtectedPeer312.Raw GeneralLatePeerFinalPeerPlan311.packet m := by
  have saved : GeneralLatePeerDirectPlan311.plan ∈ final.plans := List.mem_cons_of_mem _ List.mem_cons_self
  exact GeneralVersionedAliasReport312.from_alias (registry := registry) ⟨rfl,checked⟩ reached
    GeneralLatePeerDirectPlan311.plan GeneralLatePeerFinalPeerPlan311.plan saved
    GeneralLatePeerCurrent311.frame.center_recorded rfl GeneralLatePeerCurrent311.located
    GeneralLatePeerMerge311.alias rfl m model

end Yulang.Cycle312ActualProbe
#print axioms Yulang.Cycle312ActualProbe.root_forwarded
#print axioms Yulang.Cycle312ActualProbe.route_forwarded
#print axioms Yulang.Cycle312ActualProbe.current_raw
