import Yulang.GeneralDeclarativeRepeatedVisible348
import Yulang.GeneralWhereVersionRegression317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 36000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeRepeatedClosure348
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralWhereVersionSnapshot317 (context)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionCommit317 (core)
open GeneralWhereVersionCase317 (occ ordered_children)
open GeneralWhereVersionCompiler317 (children)
open GeneralWhereVersionJournal317 (fixed_iff)
open GeneralDeclarativeWhereTxn348 (Txn)
open GeneralDeclarativeRepeatedTxn348 (checked)
open GeneralDeclarativeRepeatedPlacement348 (keep placedView requested same_model_placement)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralDeclarativeTxnComplete348 (Done)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (ErasedEvidence LocalInstance)
open GeneralDictionaryReadback (erased_evidence_node)
open GeneralWhereVersionRegression317 (RootCertificate recorded)
open GeneralWhereOriginSupport318 (journalSources)

def Instance (m : Assignment) : LocalInstance roles :=
  fun atSite key kids =>
    (atSite = root ∧ key = declaration.id ∧ kids = children rootPlan ∧
      Txn sourceRegistry before context rootPlan ∧ RootCertificate m) ∨
    GeneralNominalVersionedEvidence231.Instance registry core m atSite key kids

theorem physical_tree (m : Assignment) (fit : Models fixed m) :
    ErasedEvidence (Instance m) root dictionary := by
  change ErasedEvidence (Instance m) root (.node declaration.id [.node leaf.id []])
  have parent := (fixed_iff m).mp fit
  have rootInstance : Instance m root declaration.id (children rootPlan) :=
    Or.inl ⟨rfl,rfl,rfl,checked,recorded m fit⟩
  apply erased_evidence_node _ _ _ _ _ rootInstance
  rw [ordered_children]
  exact .cons (erased_evidence_node _ _ _ [] []
    (Or.inr ⟨_,GeneralWhereVersionLeaf317.certificate m parent⟩) .nil) .nil

/-- One model for the original repeated declaration's corrected actual
transaction, current recursive physical certificates and ordered ordinary
child placement. The raw footprint (including historical bindings) is
preserved, but this does not certify an unchanged native solver. -/
theorem closure (m : Assignment) (fit : Models fixed m) :
    ∃ n, Models fixed n ∧
      (∀ k ∈ journalSources fixed, n k = m k) ∧
      GeneralDeclarativeHead320.Models placedView n ∧
      Placement fixed.mixed placedView occ requested ∧
      ErasedEvidence (Instance n) root dictionary ∧
      Done sourceRegistry before context rootPlan rootPlan.packet.site.occurrence.identity := by
  obtain ⟨n,raw,ordinary,placed,stays⟩ := same_model_placement m fit
  exact ⟨n,raw,fun k whereSeen => stays k (List.mem_append_right _ whereSeen),ordinary,placed,
    physical_tree n raw,GeneralDeclarativeRepeatedVisible348.completed⟩

end Yulang.GeneralDeclarativeRepeatedClosure348
