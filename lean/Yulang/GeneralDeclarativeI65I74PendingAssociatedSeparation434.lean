import Yulang.GeneralDeclarativeI65I74PendingAssociatedNoCompletion434

namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open GeneralDeclarativeLowerKnown321 (Knows Delayed knows_row)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessOrigins350 (support)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open Checker408 (Problem Result)

/-- One State, two intentional roles of the same ordinary equation:
the full graph exposes a nominal tag, but the independent source slice
does not authorize that tag as a head. The focused input is the exact
original child occurrence; this does not generalize the executable reader
to states outside its explicit scope. -/
theorem original_retained_output_is_known_raw_but_delayed_as_source434
    {s q} (o : OriginalPendingWhere434 s q) :
    Knows s.core.current.ordinary o.episode.a (.nominal o.episode.key 1) ∧
    Delayed (support (actual_episode_attachment434 o.episode)) q.demand := by
  refine ⟨knows_row (code := .nominal o.episode.key [.variable o.episode.b]) ?_ rfl,?_⟩
  · rw [o.episode.exactRows]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · refine ⟨point o.episode.a,?_,o.noIndependent⟩
    rw [o.episode.targetArg]
    exact List.mem_singleton_self _

/-- The actual entry proves both sides of the separation. In particular,
ordinary equations are not stripped before the root K2 test. -/
theorem checked_entry_reads_raw_nominal_but_derives_source_delay434
    {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.pendingAssociated w) = true) :
    ∃ o : Replay434 p, replay434 p w = some o ∧ ¬ RootCycle p.state p.root ∧
      Knows p.state.core.current.ordinary o.original.episode.a
        (.nominal o.original.episode.key 1) ∧
      Delayed (support (actual_episode_attachment434 o.original.episode)) p.root.demand := by
  obtain ⟨o,atSource,_⟩ := checked_pending_reads_actual_original_episode434 yes
  exact ⟨o,atSource,o.rootSafe,original_retained_output_is_known_raw_but_delayed_as_source434
    o.original⟩

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
