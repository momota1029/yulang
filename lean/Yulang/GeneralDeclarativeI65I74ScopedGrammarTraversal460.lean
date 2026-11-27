import Yulang.GeneralDeclarativeI65I74CompiledOpeningScope460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open InlineStructuralPolicy458 (policy)
open RoutedMixed456 (endsAtField)

/-- Independent compiled-side scope through a raw trail. Each node uses
the same state. Continuations are quantified over that exact chosen child,
not assumed for an unvisited component. A reflected opening decides
which child exists; the continuation cannot close an unsupported hop. -/
inductive ScopedRaw (s : CoreState) :
    Nat → Term → Expr → MixedPath → Nat → Term → Bool → Prop
  | stop : Inspects e → ScopedRaw s n t e [] n t false
  | down : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) n →
    AuthenticatedHop458.AtStep s.current.ordinary (policy s) n e a c next used →
    CompiledOpening s t e a →
    (∀ u, Step (queryKeys s) t (writtenAddress a) u →
      ScopedRaw s c u next rest terminal last others) →
    ScopedRaw s n t e ((a,c)::rest) terminal last (used || others)

theorem written_choice_is_unique {keys t a x y}
    (p : Step keys t a x) (q : Step keys t a y) : x = y :=
  Option.some.inj ((read_step_complete p).symm.trans (read_step_complete q))

theorem exact_scope_reifies_full_trace_by_descent {s n t e path terminal last used}
    (auth : AuthoredQuery s (writeTerm t) e)
    (inScope : ScopedRaw s n t e path terminal last used) :
    CompiledTrail s n t e path terminal last used := by
  induction inScope with
  | stop rigid => exact .stop auth rigid
  | down safe atStep scope _ ih =>
    have observed := atStep
    obtain ⟨_,_,_,_,_,actual,_⟩ := observed
    obtain ⟨u,step,child⟩ := compiled_scope_reflects_exact_selected_step auth scope actual
    exact .down auth safe atStep step (ih u step child)

theorem full_trace_reflects_exact_compiled_scope {s n t e path terminal last used}
    (trace : CompiledTrail s n t e path terminal last used) :
    ScopedRaw s n t e path terminal last used := by
  induction trace with
  | stop _ rigid => exact .stop rigid
  | down auth safe atStep step _ ih =>
    have observed := atStep
    obtain ⟨_,_,_,_,_,actual,_⟩ := observed
    have scope := (compiled_scope_iff_independent_written_step auth actual).mpr
      ⟨_,step,same_authored_compilation_at_selected_child auth step actual⟩
    refine .down safe atStep scope ?_
    intro other valid
    cases written_choice_is_unique valid step
    exact ih

theorem any_finite_scoped_field_has_exactly_its_structural_wire {s n t e path terminal last}
    (auth : AuthoredQuery s (writeTerm t) e) :
    (∃ w, readAlreadyCompiledField s n t e w = some (path,terminal,last)) ↔
    (∃ used, ScopedRaw s n t e path terminal last used) ∧
      endsAtField path terminal = true ∧ AliasCycle s.current.ordinary (observed s.current.ordinary) terminal := by
  rw [precompiled_field_iff_exact_finite_path auth]
  constructor
  · rintro ⟨⟨used,h⟩,field,raw⟩
    exact ⟨⟨used,full_trace_reflects_exact_compiled_scope h⟩,field,raw⟩
  · rintro ⟨⟨used,h⟩,field,raw⟩
    exact ⟨⟨used,exact_scope_reifies_full_trace_by_descent auth h⟩,field,raw⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
