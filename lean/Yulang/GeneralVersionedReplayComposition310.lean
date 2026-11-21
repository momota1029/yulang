import Yulang.GeneralVersionedRecursiveBridge310
import Yulang.GeneralSharedNamedCompiler310

set_option backward.isDefEq.respectTransparency false
/-! Rebuilding once from recorded provenance or twice via two genuine
ordinary extensions gives literally the same current packet. -/
namespace Yulang.GeneralVersionedReplayComposition310
open GeneralDictionaryOrdinaryTransport (extend extendState)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedInstallation231 (replayPlan)

theorem context (ctx : GeneralNominalCandidates.Context) (a b : List Nat)
    (x y : List (PresenceNormalForm.Atom Nat)) (p q : List GeneralNominalIdentities.Origin) :
    extend (extend ctx a x p) b y q = extend ctx (a ++ b) (x ++ y) (p ++ q) := by
  simp only [extend,extendState,List.append_assoc]

theorem compose (old : Plan roles) (a b : List Nat)
    (x y : List (PresenceNormalForm.Atom Nat)) (p q : List GeneralNominalIdentities.Origin) :
    extendedPlan b y q (extendedPlan a x p old) = extendedPlan (a ++ b) (x ++ y) (p ++ q) old := by
  unfold extendedPlan extendedPacket extend extendState
  rw [List.append_assoc,List.append_assoc,List.append_assoc]

end Yulang.GeneralVersionedReplayComposition310

namespace Yulang.GeneralSharedNamedHistoryReplay310
open GeneralNominalVersionedInstallation231 (reserved atoms allocated replayPlan)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralSharedNamedSource310 (root registry checked compiled impl)
open GeneralSharedNamedPlan310 (plan kids)
open GeneralSharedNamedMerge310 (merged added reached)
open GeneralSharedNamedCurrent310 (parent current_parent)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarationExamples (roles)

theorem composed_parent : parent =
    extendedPlan (reserved plan.packet) (atoms plan.packet ++ added) (allocated plan.packet) plan := by
  change extendedPlan [] added [] (replayPlan plan) = _
  unfold replayPlan
  rw [GeneralVersionedReplayComposition310.compose,List.append_nil,List.append_nil]

theorem coverage :
    GeneralVersionedRecursiveBridge310.ReplayFrame registry merged root impl.id kids := by
  refine ⟨plan,List.mem_cons_self,reserved plan.packet,atoms plan.packet ++ added,allocated plan.packet,
    composed_parent ▸ current_parent,?_⟩
  have cert := GeneralSharedNamedCurrent310.parent_certificate _ GeneralSharedNamedMerge310.inhabited
  exact composed_parent ▸ cert.children_eq

/-- A factual occurrence of the generic replay branch with two child
    dictionaries; stability and prospective parent installability do not
    enter its proof. -/
theorem replayed_tree (m : Assignment) (valid : Models merged m) :
    Evidence compiled merged.core m root (.node 1 [.node 2 [],.node 2 []]) ∧
    ∀ child ∈ kids, Generated merged.core.erased.current root child := by
  obtain ⟨old,stored,rs,added',own,frame,order⟩ := coverage
  have left := GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,GeneralSharedNamedCurrent310.receiver_certificate .low m valid⟩
  have right := GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,GeneralSharedNamedCurrent310.receiver_certificate .high m valid⟩
  obtain ⟨tree,edges⟩ := GeneralVersionedHistoryEvidence310.from_recorded_extension ⟨rfl,checked⟩ reached
    stored rs added' own frame order valid (.cons left (.cons right .nil))
  exact ⟨tree,edges (.inl rfl)⟩

end Yulang.GeneralSharedNamedHistoryReplay310
