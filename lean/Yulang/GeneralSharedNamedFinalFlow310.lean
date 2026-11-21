import Yulang.GeneralSharedNamedCompiler310
import Yulang.GeneralVersionedExplicitFromHolds310
import Yulang.GeneralVersionedReplayComposition310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 16000000
namespace Yulang.GeneralSharedNamedFinalFlow310
open GeneralSharedNamedSource310 (root registry compiled checked impl associated leafBody lowRule highRule lowOut highOut)
open GeneralSharedNamedPlan310 (z loSite hiSite loSig hiSig kids)
open GeneralSharedNamedMerge310 (merged added reached)
open GeneralSharedNamedCurrent310 (parent receiver parent_certificate receiver_certificate)
open GeneralSharedNamedLeaf310 (Side site decl)
open GeneralNominalVersionedEvidence231 (Evidence Certificate)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedFrame231 (clauseChild)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects (compileBody bodyVariables)
open GeneralDictionaryAssociatedProvenance (Body Supplies supplies_unique)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

theorem current_occurrence_low : clauseChild parent.packet lowRule loSig = loSite.occurrence := by
  change clauseChild (GeneralNominalVersionedTransport231.extendedPacket [] added []
    GeneralSharedNamedEvidence310.parentPlan.packet) lowRule loSig = _
  rw [GeneralNominalVersionedTransport231.clauseChild_eq]
  simpa only [show (Side.low = .low) from rfl,ite_true] using (GeneralSharedNamedDependence310.parent_receiver .low).symm

theorem current_occurrence_high : clauseChild parent.packet highRule hiSig = hiSite.occurrence := by
  change clauseChild (GeneralNominalVersionedTransport231.extendedPacket [] added []
    GeneralSharedNamedEvidence310.parentPlan.packet) highRule hiSig = _
  rw [GeneralNominalVersionedTransport231.clauseChild_eq]
  simpa only [show Side.high ≠ .low from by decide,ite_false] using (GeneralSharedNamedDependence310.parent_receiver .high).symm

theorem current_outputs (side : Side) (m : Assignment) (valid : Models merged m) :
    ∃ body expr,
      Supplies roles (receiver side).packet.declaration 1 body ∧ compileBody (receiver side) body = some expr ∧
      Equivalent (m 1).1 (value (bodyVariables (receiver side) m body) .actual expr) := by
  have parentProof := parent_certificate m valid
  have ask : (⟨0,1⟩ : GeneralSourceState.Output) ∈ root.demand.outputs := List.mem_singleton_self _
  have assoc : associated ∈ parent.packet.declaration.associated := List.mem_singleton_self _
  have translated : compileBody parent (.explicit associated) = some (.variable 5) := rfl
  have names : 5 ∈ parent.packet.declaration.outputNames := by decide +kernel
  cases side with
  | low =>
    have cert := current_occurrence_low.symm ▸ receiver_certificate .low m valid
    exact GeneralVersionedOutputHandoff310.parent_child loSig (List.mem_singleton_self lowOut)
      names rfl parentProof cert ask assoc rfl translated
  | high =>
    have cert := current_occurrence_high.symm ▸ receiver_certificate .high m valid
    exact GeneralVersionedOutputHandoff310.parent_child hiSig (List.mem_singleton_self highOut)
      names rfl parentProof cert ask assoc rfl translated

theorem same_output_by_actual_body (side : Side) (m : Assignment) (valid : Models merged m) :
    Supplies roles (receiver side).packet.declaration 1 (.explicit leafBody) ∧
    compileBody (receiver side) (.explicit leafBody) = some (.primitive (.scalar .int) []) ∧
    Equivalent (m 1).1 (.base .int) := by
  have given : Supplies roles (receiver side).packet.declaration 1 (.explicit leafBody) :=
    .explicit _ (List.mem_singleton_self _) rfl
  have compile : compileBody (receiver side) (.explicit leafBody) = some (.primitive (.scalar .int) []) := by
    cases side <;> rfl
  obtain ⟨body,expr,known,done,same⟩ := current_outputs side m valid
  have eq := supplies_unique roles (receiver side).packet.declaration
    (receiver side).packet.checked.identified.2.2.1 1 body (.explicit leafBody) known given
  subst body
  have equation := Option.some.inj (done.symm.trans compile)
  subst expr
  exact ⟨given,compile,same⟩

theorem child_without_live_assumption (side : Side) (m : Assignment) (valid : Models merged m) :
    Certificate compiled merged.core m (site side).occurrence (decl side).id [] (receiver side) := by
  have old := receiver_certificate side m valid
  refine GeneralVersionedExplicitFromHolds310.certificate old.frame old.children_eq old.packet ?_
  intro output member
  rw [GeneralSharedNamedLeaf310.named_requests side] at member
  cases List.mem_singleton.mp member
  refine ⟨leafBody,List.mem_singleton_self _,rfl,.primitive (.scalar .int) [],?_⟩
  cases side <;> rfl

theorem certified_package (m : Assignment) (valid : Models merged m) :
    Evidence compiled merged.core m root (.node 1 [.node 2 [],.node 2 []]) ∧
    (∀ side, Supplies roles (receiver side).packet.declaration 1 (.explicit leafBody) ∧
      Equivalent (m 1).1 (.base .int)) ∧
    All₂ (Evidence compiled merged.core m) kids [.node 2 [],.node 2 []] := by
  have left := GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,child_without_live_assumption .low m valid⟩
  have right := GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,child_without_live_assumption .high m valid⟩
  have both : All₂ (Evidence compiled merged.core m) kids [.node 2 [],.node 2 []] := .cons left (.cons right .nil)
  refine ⟨(GeneralSharedNamedHistoryReplay310.replayed_tree m valid).1,?_,both⟩
  intro side
  have fact := same_output_by_actual_body side m valid
  exact ⟨fact.1,fact.2.2⟩

end Yulang.GeneralSharedNamedFinalFlow310
