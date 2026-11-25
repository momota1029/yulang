import Yulang.GeneralDeclarativeI65I73UnifiedControls408

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Summarizes)

noncomputable def encodedLedger {s q d} (ledger : Ledger s q d) : List Write :=
  Ledger.rec
    (motive_1 := fun {_ _} _ => List Write)
    (motive_2 := fun {_ _} _ => List Write)
    (fun event _ children => encodedEventWrites event ++ children)
    [] (fun _ _ a b => a ++ b) ledger

noncomputable def encodedLedgerForest {s qs ds} (ledger : LedgerForest s qs ds) : List Write :=
  LedgerForest.rec
    (motive_1 := fun {_ _} _ => List Write)
    (motive_2 := fun {_ _} _ => List Write)
    (fun event _ children => encodedEventWrites event ++ children)
    [] (fun _ _ a b => a ++ b) ledger

/-- Successful dictionaries use the same literal output rows preserved
by the diagnostic trace, in authored parent/where order. This holds
also for R0 derivations with writes even though C408's current finite
witness variants do not yet check a nonempty write list. -/
theorem canonical_dictionary_writes_equal_report_trace408 {s q t e d}
    {trace : SourceTrace R0 s q t e} (tree : I72.GeneralTree trace d) :
    encodedLedger tree.ledger = traceWrites trace := by
  exact I72.GeneralTree.rec (R := R0) (s := s)
    (motive_1 := fun {_ _ _} raw _ lowered => encodedLedger lowered.ledger = traceWrites raw)
    (motive_2 := fun {_ _} raw _ lowered => encodedLedgerForest lowered.ledger = forestWrites raw)
    (fun {_} {_} {_} {_} {event} {_} {_} {_} {_} _ _ children =>
      congrArg (fun rest => encodedEventWrites event ++ rest) children)
    rfl (fun _ _ first rest => congr (congrArg List.append first) rest) tree

theorem accepted_selected_reports_the_same_literal_ledger408 (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) {d : Dictionary} (selected : r.verdict = .selected d) :
    ∃ e, ∃ trace : SourceTrace R0 p.state p.root r.tree e,
      ∃ tree : I72.GeneralTree trace d,
        CanonicalReplay tree tree.ledger ∧ r.writes = encodedLedger tree.ledger ∧
        ∀ m, Fits p.state m → DictionaryEvidence p.state m p.root d := by
  obtain ⟨e,trace,summary,writes⟩ := (check_sound p r w accepted).1
  rw [selected] at summary
  obtain ⟨tree,canonical,_,all⟩ := R0_trace_has_one_canonical_ledger407 trace summary
  exact ⟨e,trace,tree,canonical,writes.trans (canonical_dictionary_writes_equal_report_trace408 tree).symm,all⟩

theorem literal_output_wire_keeps_original_body_target_and_indices408 {s q}
    (event : Event s q) (i : Fin q.demand.outputs.length) :
    (encodedEventWrites event)[i.val]? =
      some ⟨q.occurrence,event.frame.ordinal,i.val,q.demand.outputs[i],(event.outputs i).body,
        encodeRhs (event.outputs i).rhs⟩ := by
  rw [encodedEventWrites,List.getElem?_ofFn,dite_eq_left i.isLt]


/-- The same literal derivation can be fixed before quantifying over
models. No replay or witness is selected using model satisfaction. -/
theorem accepted_report_fixes_one_trace_before_every_model408
    (p : Problem) (r : Result) (w : Witness) (accepted : check p r w = true) :
    ∃ e, ∃ trace : SourceTrace R0 p.state p.root r.tree e,
      Summarizes r.tree r.verdict ∧ r.writes = traceWrites trace ∧
      ∀ m, Fits p.state m → TraceMeaning p.state m trace := by
  obtain ⟨e,trace,summary,writes⟩ := (check_sound p r w accepted).1
  exact ⟨e,trace,summary,writes,mixed_R0_trace_model_meaning408 trace⟩

end Yulang.GeneralDeclarativeI65.I72.Check408
