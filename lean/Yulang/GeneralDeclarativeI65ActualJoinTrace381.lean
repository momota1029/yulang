import Yulang.GeneralDeclarativeI65WrittenJoinInversion381

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Classify Frontier Tree Dictionary Result Resolves Summarizes)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule)
open GeneralDeclarativeDemand320 (Demand)

/-- The local inversion identifies the literal chosen children, not
merely the length or the keys of the finished dictionary. -/
theorem extract_same_C357_join_event381 {s : State}
    (scope : WrittenJoinHeadScope381 s) {key : Nat} {ds : List Demand}
    (actual : Rule s.current scope.request.demand (.selected key ds)) :
    ∃ event : WrittenJoinEvent381 s,
      ActualWrittenJoin381 s scope.request (.selected key (children scope.request ds)) event := by
  obtain ⟨event,root,_,chosen,written⟩ := invert_actual_C357_at_written_join381 scope actual
  injection chosen with exactKey exactChildren
  rw [root,← exactKey,← exactChildren] at written
  exact ⟨event,written⟩

mutual
/-- Scoped input derivation: actual local C357 derivations plus their
independently authored head facts and exact child requests. This is
not a global admission rule or an alternative to the frozen theorem. -/
inductive ActualC357JoinTrace381 (s : State) : Request → Tree → Type where
  | selected (scope : WrittenJoinHeadScope381 s)
      (chosen : Rule s.current scope.request.demand (.selected key demands)) :
      ActualC357JoinForest381 s (children scope.request demands) trees →
      ActualC357JoinTrace381 s scope.request (.selected key trees)

inductive ActualC357JoinForest381 (s : State) : List Request → List Tree → Type where
  | nil : ActualC357JoinForest381 s [] []
  | cons : ActualC357JoinTrace381 s q t → ActualC357JoinForest381 s qs ts →
      ActualC357JoinForest381 s (q::qs) (t::ts)
end

/-- Extract all written source events from an already given scoped
C357 derivation. Every recursive child keeps the literal request
indices; no diagnosis is interpreted as evidence of what was read. -/
theorem actual_C357_join_trace_extracts_events381
    {s : State} {q : Request} {t : Tree} (trace : ActualC357JoinTrace381 s q t) :
    Nonempty (SourceEventTrace381 (ActualWrittenJoin381 s) q t) := by
  exact ActualC357JoinTrace381.rec
    (motive_1 := fun root tree _ => Nonempty (SourceEventTrace381 (ActualWrittenJoin381 s) root tree))
    (motive_2 := fun roots trees _ => Nonempty (SourceEventForest381 (ActualWrittenJoin381 s) roots trees))
    (fun scope chosen _ more => by
      obtain ⟨actual,written⟩ := extract_same_C357_join_event381 scope chosen
      obtain ⟨children⟩ := more
      exact ⟨.selected actual written children⟩)
    ⟨.nil⟩
    (fun _ _ ⟨first⟩ ⟨rest⟩ => ⟨.cons first rest⟩)
    trace

/-- The independent scoped source derivation gives the exact selected
diagnosis and its actual ordered source trace. Other constructor and
diagnostic cases of the language are not covered by this theorem. -/
theorem actual_C357_join_selected_summary_trace381
    {s : State} {q : Request} {t : Tree} {d : Dictionary}
    (trace : ActualC357JoinTrace381 s q t) (summary : Summarizes t (.selected d)) :
    Classify (Rule s.current) q.demand (.selected d) ∧
      (∃ _events : SourceEventTrace381 (ActualWrittenJoin381 s) q t,
        Resolves (ProjectEventRule381 (ActualWrittenJoin381 s)) q t ∧
        Summarizes t (.selected d)) := by
  obtain ⟨events⟩ := actual_C357_join_trace_extracts_events381 trace
  exact ⟨scoped_join_classification_uses_actual_C357_381 events summary,
    events,explicit_source_events_project381 events,summary⟩

end Yulang.GeneralDeclarativeI65
