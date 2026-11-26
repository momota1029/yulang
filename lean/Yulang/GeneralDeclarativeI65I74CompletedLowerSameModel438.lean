import Yulang.GeneralDeclarativeI65I74CompletedLowerEntry438

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)

/-- The literal producer derivation already stored in this root's
support has its old mathematical dictionary in the *same* model in
which the new head interprets the fixed output. This does not turn
that producer into one of the consumer's where children. -/
theorem actual_producer_and_consumer_share_one_model438 {s q}
    (a : Selected18 s q) (m : I72.Model) (fit : Fits s m) :
    I72.DictionaryEvidence s m a.invocation.chosen.need.producer a.invocation.chosen.need.dictionary ∧
      a.head.Means m ∧ DictionaryEvidence18 s m q a.dictionary := by
  let actual := a.invocation.chosen.producer
  obtain ⟨_,_,meaning⟩ := authored_native_dictionary_reuses_given_trace405 actual.source actual.completion
  exact ⟨meaning m fit,completed_head_has_literal_original_meaning438 a.head m fit,
    completed_selected_evidence438 a m fit⟩

theorem checked_completed_has_original_same_model_dictionary438 {p : Problem} {r : Result} {w : Wire438}
    (accepted : check p r (.completedLower w) = true) :
    ∃ a : Replay438 p.state p.root w,
      replay438 p.state p.root w = some a ∧ r = a.selected.report ∧
      ∀ m : I72.Model, I72.Fits p.state m →
        I72.DictionaryEvidence p.state m a.selected.invocation.chosen.need.producer
          a.selected.invocation.chosen.need.dictionary ∧
        a.selected.head.Means m ∧ DictionaryEvidence18 p.state m p.root a.selected.dictionary := by
  obtain ⟨a,replayed,report⟩ := checked_completed_reads_exact_report438 accepted
  exact ⟨a,replayed,report,actual_producer_and_consumer_share_one_model438 a.selected⟩

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
