import Yulang.GeneralDeclarativeI65SourceEventTrace381
import Yulang.GeneralDeclarativeWitnessClassifyVariance357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Frontier Tree Dictionary Result Resolves Summarizes)
open GeneralDeclarativeWitnessClassifyVariance357 (JoinedLocal roleView)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

/-- Exact old independent authored unary-join event, not a new rule of
selection. It keeps the request occurrence and the actual selected row,
not merely the normalized payload or dictionary key. No model occurs. -/
structure WrittenJoinEvent381 (s : State) where
  request : Request
  row : Declaration
  demands : List Demand
  authored : JoinedLocal s.current request.demand row demands

inductive ActualWrittenJoin381 (s : State) :
    Request → Frontier Request → WrittenJoinEvent381 s → Prop where
  | authored (e : WrittenJoinEvent381 s) :
      ActualWrittenJoin381 s e.request (.selected e.row.id (children e.request e.demands)) e

theorem written_join_original_visible_order381 {s : State} (e : WrittenJoinEvent381 s) :
    visible s e.request = [e.row] :=
  e.authored.single

theorem demand_projection_preserves_literal_children381 (q : Request) (ds : List Demand) :
    (children q ds).map Request.demand = ds := by
  simp [children,List.map_map,Function.comp_def]

/-- Erasing the request occurrence and retaining exact child demand
order from the authored events yields a real C357 derivation. Only its
authored join constructor is used. No compiler/receipt success is
converted back into the declaration's head decision. -/
theorem authored_join_events_to_actual_C357_381 {s : State} {q : Request} {t : Tree}
    (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t) :
    Resolves (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current) q.demand t := by
  exact SourceEventTrace381.rec
    (motive_1 := fun root tree _ =>
      Resolves (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current) root.demand tree)
    (motive_2 := fun roots trees _ =>
      All₂ (Resolves (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current))
        (roots.map Request.demand) trees)
    (fun _ blocked => nomatch blocked)
    (fun _ blocked => nomatch blocked)
    (fun _ blocked => nomatch blocked)
    (fun event tagged _ rest => by
      cases tagged
      rw [demand_projection_preserves_literal_children381] at rest
      exact .selected (.join event.authored) rest)
    .nil
    (fun _ _ now later => .cons now later)
    trace

theorem scoped_join_classification_uses_actual_C357_381 {s : State} {q : Request} {t : Tree}
    {d : Dictionary} (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t)
    (summary : Summarizes t (.selected d)) :
    CommonRoleOutermostResolver.Classify
      (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current) q.demand (.selected d) :=
  ⟨t,authored_join_events_to_actual_C357_381 trace,summary⟩

/-- The S01 outer interface specialized to the real declared unary-join
constructor, with no model, checker result, or old ordinary rule.
It does not interpret any other C357 case or supply the generalized
source interpretation. -/
theorem actual_written_join_scope_unpacks381 {s : State} {q : Request} {d : Dictionary}
    (h : CommonRoleOutermostResolver.Classify
      (ProjectEventRule381 (ActualWrittenJoin381 s)) q (.selected d)) :
    ∃ t : Tree, Nonempty (SourceEventTrace381 (ActualWrittenJoin381 s) q t) ∧
      Resolves (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current) q.demand t ∧
      Summarizes t (.selected d) := by
  obtain ⟨t,_,⟨trace⟩,summary⟩ := event_classification_unpacks381 h
  exact ⟨t,⟨trace⟩,authored_join_events_to_actual_C357_381 trace,summary⟩

end Yulang.GeneralDeclarativeI65
