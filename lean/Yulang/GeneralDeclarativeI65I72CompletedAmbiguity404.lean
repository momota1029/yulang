import Yulang.GeneralDeclarativeI65I72CompletedNativeStability404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes)
open GeneralDeclarations (Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)

structure SupportedAmbiguity404 (s : State) (q : Request) (needs : List (OutputNeed s)) where
  input : ∀ a ∈ q.demand.arguments, InputAccess404 s needs a
  checked : Checked (authoredRegistry s.core.current)
  covered : ∀ d ∈ visible s.core q, DeclarationCovered s.core.current.environment d
  allVisible : ∀ d ∈ visible s.core q, RepeatedRow403 q d
  two : 2 ≤ (visible s.core q).length

def completedChoiceSource404 : SourcePrimitives where
  elected := completedNativePrioritySource404.elected
  other := fun s q verdict needs =>
    completedNativePrioritySource404.other s q verdict needs ∨
      (verdict = .ambiguous ∧ Nonempty (SupportedAmbiguity404 s q needs))

theorem completed_choice_keeps_fixed_rows404 : KeepsFixedOutputs404 completedChoiceSource404 :=
  native_priority_keeps_exact_rows404

noncomputable def preserve_completed_native_sources404 {s q t e}
    (trace : SourceTrace completedNativePrioritySource404 s q t e) :
    SourceTrace completedChoiceSource404 s q t e :=
  SourceTrace.rec (R := completedNativePrioritySource404) (s := s)
    (motive_1 := fun q t e _ => SourceTrace completedChoiceSource404 s q t e)
    (motive_2 := fun qs ts _ => WhereForest completedChoiceSource404 s qs ts)
    (motive_3 := fun needs _ => SupportForest completedChoiceSource404 s needs)
    (fun cycle => .rootK2 cycle)
    (fun verdict safe old _ child => .other verdict safe (.inl old) child)
    (fun e safe rule _ _ support kids => .selected e safe rule support kids)
    .nil (fun _ _ first rest => .cons first rest)
    .nil (fun _ completed typed _ source rest => .cons source completed typed rest) trace

private theorem remove_completed_ambiguity_from_success404 {s q t e}
    (trace : SourceTrace completedChoiceSource404 s q t e) :
    ∀ d, Summarizes t (.selected d) →
      Nonempty (SourceTrace completedNativePrioritySource404 s q t e) := by
  exact SourceTrace.rec (R := completedChoiceSource404) (s := s)
    (motive_1 := fun q t e _ => ∀ d, Summarizes t (.selected d) →
      Nonempty (SourceTrace completedNativePrioritySource404 s q t e))
    (motive_2 := fun qs ts _ => ∀ ds : List Dictionary, All₂ Summarizes ts (ds.map Result.selected) →
      Nonempty (WhereForest completedNativePrioritySource404 s qs ts))
    (motive_3 := fun needs _ => Nonempty (SupportForest completedNativePrioritySource404 s needs))
    (fun _ _ proves => by cases proves)
    (fun verdict _ _ _ _ _ proves => by cases verdict <;> cases proves)
    (fun event safe chose _ _ recSupport recChildren _ summary => by
      cases summary with
      | selected localChildren merged =>
        cases merged with
        | selected exacts =>
          rw [exacts] at localChildren
          obtain ⟨support⟩ := recSupport
          obtain ⟨children⟩ := recChildren _ localChildren
          exact ⟨.selected event safe chose support children⟩)
    (fun ds proof => by cases ds with
      | nil => exact ⟨.nil⟩
      | cons _ _ => cases proof)
    (fun _ _ one rest ds exacts => by
      cases ds with
      | nil => cases exacts
      | cons d ds =>
        cases exacts with
        | cons chosen all =>
          obtain ⟨first⟩ := one d chosen
          obtain ⟨last⟩ := rest ds all
          exact ⟨.cons first last⟩)
    ⟨.nil⟩
    (fun _ chosen literal _ actual rest => by
      obtain ⟨before⟩ := actual _ chosen
      obtain ⟨after⟩ := rest
      exact ⟨.cons before chosen literal after⟩) trace

theorem completed_ambiguity_preserves_exact_selection404 {s q d} :
    Classifies completedChoiceSource404 s q (.selected d) ↔
      Classifies completedNativePrioritySource404 s q (.selected d) := by
  constructor
  · rintro ⟨t,e,⟨trace⟩,summary⟩
    exact ⟨t,e,remove_completed_ambiguity_from_success404 trace d summary,summary⟩
  · rintro ⟨t,e,⟨trace⟩,summary⟩
    exact ⟨t,e,⟨preserve_completed_native_sources404 trace⟩,summary⟩

theorem finite_completed_choice_dictionary_sound404 : DictionarySound completedChoiceSource404 :=
  fun s q d chosen m fit => completed_native_priority_dictionary_sound404 s q d
    (completed_ambiguity_preserves_exact_selection404.mp chosen) m fit

theorem all_visible_candidates_ambiguous_after_actual_support404 {s q needs}
    (front : SupportedAmbiguity404 s q needs) (safe : ¬RootCycle s q)
    (support : SupportForest completedChoiceSource404 s needs) :
    Classifies completedChoiceSource404 s q .ambiguous ∧
      ∀ a ∈ q.demand.arguments, Nonempty (ReadyInput404 completedChoiceSource404 s a) :=
  ⟨⟨.ambiguous,none,⟨.other .ambiguous safe (.inr ⟨rfl,⟨front⟩⟩) support⟩,.ambiguous⟩,
    fun a seen => ⟨recover_original_input404 completed_choice_keeps_fixed_rows404 support (front.input a seen)⟩⟩

theorem all_visible_variable_ambiguity_cannot_be_selected404 {s q needs}
    (front : SupportedAmbiguity404 s q needs) {d} :
    ¬ Classifies completedChoiceSource404 s q (.selected d) := by
  rintro ⟨t,_,⟨trace⟩,summary⟩
  cases trace with
  | rootK2 => cases summary
  | other v _ _ _ => cases v <;> cases summary
  | selected event safe chose support kids =>
    have unique : visible s.core q = [event.frame.decl] := by
      rcases chose with old|new
      · obtain ⟨r⟩ := old.2.1
        exact r.elected.sole
      · obtain ⟨r⟩ := new.1
        exact r.choice.sole
    have count := front.two
    simp [unique] at count

/-- No consumer output, capture equality, or chosen body is tested
to get the ambiguity when the one actual input comes from a full
selected producer. Its proof uses the original exact producer event. -/
theorem actual_completed_producer_opens_visible_ambiguity404
    {s producer q t e dict a}
    (trace : SourceTrace variableWithNativeK2403 s producer t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin producer.demand.outputs.length)
    (literal : LiteralInputNeed404 s a (needOfSelected404 e dict i))
    (input : q.demand.arguments = [a]) (bounds : Bounds s.core.current.ordinary a)
    (checked : Checked (authoredRegistry s.core.current))
    (covered : ∀ d ∈ visible s.core q, DeclarationCovered s.core.current.environment d)
    (allVisible : ∀ d ∈ visible s.core q, RepeatedRow403 q d)
    (two : 2 ≤ (visible s.core q).length) (safe : ¬ RootCycle s q) :
    Classifies completedChoiceSource404 s q .ambiguous ∧
      ∀ d, ¬ Classifies completedChoiceSource404 s q (.selected d) := by
  let front : SupportedAmbiguity404 s q [needOfSelected404 e dict i] :=
    ⟨fun b seen => by
      rw [input] at seen
      cases List.mem_singleton.mp seen
      exact .viaOutput 0 rfl literal bounds, checked,covered,allVisible,two⟩
  let origin := preserve_completed_native_sources404
    (preserve_completed_lower_when_admitting_native404 (preserve_c403_derivation404 trace))
  have stored : SupportForest completedChoiceSource404 s [needOfSelected404 e dict i] :=
    .cons origin done rfl .nil
  exact ⟨(all_visible_candidates_ambiguous_after_actual_support404 front safe stored).1,
    fun _ => all_visible_variable_ambiguity_cannot_be_selected404 front⟩

end Yulang.GeneralDeclarativeI65.I72
