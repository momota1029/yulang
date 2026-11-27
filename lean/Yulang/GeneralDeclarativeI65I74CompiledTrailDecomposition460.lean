import Yulang.GeneralDeclarativeI65I74PrecompiledField460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery)
open InlineStructuralPolicy458 (policy)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RoutedMixed456 (endsAtField)

theorem compiled_trace_is_root_authored {s root t e path terminal last used}
    (h : CompiledTrail s root t e path terminal last used) :
    AuthoredQuery s (writeTerm t) e := by
  cases h with
  | stop q => exact q
  | down q => exact q

theorem independently_aligned_lexical_and_raw_trails_compose {s root t e path terminal last used}
    (seed : AuthoredQuery s (writeTerm t) e)
    (raw : AuthenticatedHop458.Trail s.current.ordinary (policy s) root e path terminal used)
    (written : CoordinateWalk (fun _ => queryKeys s) root t path terminal last) :
    CompiledTrail s root t e path terminal last used := by
  induction raw generalizing t with
  | stop rigid =>
    cases written
    exact .stop seed rigid
  | down safe h path ih =>
    cases written with
    | down step rest =>
      have seen := h
      obtain ⟨_,_,_,_,_,actual,_⟩ := seen
      exact .down seed safe h step (ih (same_authored_compilation_at_selected_child seed step actual) rest)

theorem authored_trail_normal_form {s root t e path terminal last used} :
    CompiledTrail s root t e path terminal last used ↔
      AuthoredQuery s (writeTerm t) e ∧
      AuthenticatedHop458.Trail s.current.ordinary (policy s) root e path terminal used ∧
      CoordinateWalk (fun _ => queryKeys s) root t path terminal last := by
  constructor
  · intro found
    have j := compiled_trace_has_structural_joint_trace found
    exact ⟨compiled_trace_is_root_authored found,joint_has_actual_raw_trace j,
      joint_has_exact_written_path j⟩
  · rintro ⟨seed,raw,written⟩
    exact independently_aligned_lexical_and_raw_trails_compose seed raw written

theorem no_payload_can_stand_in_for_a_selected_field {s root t e path terminal last}
    (h : CompiledField s root t e path terminal last) :
    path ≠ [] ∧ ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) root ∧
      AliasCycle s.current.ordinary (observed s.current.ordinary) terminal := by
  obtain ⟨⟨_,trace⟩,ends,raw⟩ := h
  have wired := compiled_trace_has_structural_joint_trace trace
  have ex : ExactFieldPath s.current.ordinary (policy s) (fun _ => queryKeys s)
      inheritedCompilerPlacement root t e path terminal last :=
    ⟨⟨_,wired⟩,ends,raw⟩
  refine ⟨?_,(exact_joint_field_is_an_existing_raw_visit ex).2⟩
  intro eq
  simp [eq,endsAtField] at ends
end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
