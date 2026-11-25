import Yulang.GeneralDeclarativeI65I74X6AmbiguousPriority417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes)
open Checker408 (Result)

/-- The ambiguity rule cannot manufacture a successful dictionary or a
producer's output. For a successful tree, replay the same events,
where order and fixed-write list in R8, including all finite producer
dependencies, without changing any proof index. -/
theorem successfulTraceWasAlreadyR8 {s q t e} (actual : SourceTrace R9 s q t e)
    (d : Dictionary) (selected : Summarizes t (.selected d)) :
    Nonempty {prior : SourceTrace PlainMerged416.R8 s q t e //
      PlainMerged416.writes prior = writes actual} := by
  exact SourceTrace.rec (R := R9) (s := s)
    (motive_1 := fun q t e now => ∀ d, Summarizes t (.selected d) →
      Nonempty {a : SourceTrace PlainMerged416.R8 s q t e // PlainMerged416.writes a = writes now})
    (motive_2 := fun qs ts now => ∀ (ds : List Dictionary),
      All₂ Summarizes ts (ds.map CommonRoleOutermostResolver.Result.selected) →
      Nonempty {a : WhereForest PlainMerged416.R8 s qs ts //
        PlainMerged416.forestWrites a = forestWrites now})
    (motive_3 := fun needs _ => Nonempty (SupportForest PlainMerged416.R8 s needs))
    (fun _ _ impossible => by cases impossible)
    (fun v _ _ _ _ _ impossible => by cases v <;> cases impossible)
    (fun e safe rule _ nowKids lower whereEq _ summary => by
      cases summary with
      | selected ordered combine =>
        cases combine with
        | selected pointwise =>
          rw [pointwise] at ordered
          obtain ⟨oldKids⟩ := whereEq _ ordered
          obtain ⟨lower⟩ := lower
          refine ⟨⟨.selected e safe rule lower oldKids.val,?_⟩⟩
          change Check408.encodedEventWrites e ++ PlainMerged416.forestWrites oldKids.val =
            Check408.encodedEventWrites e ++ forestWrites nowKids
          rw [oldKids.property])
    (fun ds pre => by
      cases ds with
      | nil => exact ⟨⟨.nil,rfl⟩⟩
      | cons => cases pre)
    (fun nowFirst nowRest first rest ds ordered => by
      cases ds with
      | nil => cases ordered
      | cons d ds =>
        cases ordered with
        | cons head tail =>
          obtain ⟨a⟩ := first d head
          obtain ⟨b⟩ := rest ds tail
          refine ⟨⟨.cons a.val b.val,?_⟩⟩
          change PlainMerged416.writes a.val ++ PlainMerged416.forestWrites b.val =
            writes nowFirst ++ forestWrites nowRest
          rw [a.property,b.property])
    ⟨.nil⟩
    (fun _ summary receipt _ first rest => by
      obtain ⟨a⟩ := first _ summary
      obtain ⟨b⟩ := rest
      exact ⟨.cons a.val summary receipt b⟩)
    actual d selected

theorem successful_report_unchanged417 {s q} {r : Result} {d : Dictionary}
    (summary : r.verdict = .selected d) :
    ClassifiedAs s q r ↔ PlainMerged416.ClassifiedAs s q r := by
  constructor
  · rintro ⟨event,owned,computed,exactWrites⟩
    obtain ⟨proof⟩ := successfulTraceWasAlreadyR8 owned d (summary ▸ computed)
    exact ⟨event,proof.val,computed,exactWrites.trans proof.property.symm⟩
  · exact existing_exact_report_lifts417

theorem no_new_successful_dictionary417 {s q d} :
    I72.Classifies R9 s q (.selected d) ↔ I72.Classifies PlainMerged416.R8 s q (.selected d) := by
  constructor
  · rintro ⟨t,e,⟨trace⟩,summary⟩
    obtain ⟨prior⟩ := successfulTraceWasAlreadyR8 trace d summary
    exact ⟨t,e,⟨prior.val⟩,summary⟩
  · rintro ⟨t,e,⟨trace⟩,summary⟩
    exact ⟨t,e,⟨(liftTrace trace).val⟩,summary⟩

theorem exactly_the_ambiguity_classifies_for_actual_X6_417 {s q}
    (a : Ambiguous s q) (outcome : CommonRoleOutermostResolver.Result) :
    I72.Classifies R9 s q outcome ↔ outcome = .ambiguous := by
  constructor
  · rintro ⟨t,e,⟨trace⟩,summary⟩
    obtain ⟨rfl,_⟩ := actual_X6_has_only_ambiguity_in_R9_417 a trace
    cases summary
    rfl
  · rintro rfl
    exact exact_report_is_R9_classification417 (both_actual_matches_classify_as_ambiguity417 (p := ⟨s,q⟩) a)

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
