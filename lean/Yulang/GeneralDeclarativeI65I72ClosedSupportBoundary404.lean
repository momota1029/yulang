import Yulang.GeneralDeclarativeI65I72CompletedAmbiguity404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Summarizes Tree)
open GeneralDeclarativeWhere319 (Capture)

/-- A complete classifier result itself gives the original selected
event, retains all its lower producer proofs, and can now back an
exact output read of a later demand. This works for C404 producers,
not only the authored seed branch from C403. -/
theorem any_selected_producer_supports_its_original_outputs404 {R s q d}
    (chosen : Classifies R s q (.selected d)) :
    ∃ (t : Tree) (e : Event s q),
      Nonempty (SourceTrace R s q t (some e)) ∧ Summarizes t (.selected d) ∧
      ∀ i : Fin q.demand.outputs.length, Nonempty (SupportForest R s [needOfSelected404 e d i]) := by
  obtain ⟨t,event,⟨trace⟩,summary⟩ := chosen
  cases event with
  | none =>
    cases trace with
    | rootK2 => cases summary
    | other verdict _ _ _ => cases verdict <;> cases summary
  | some actual =>
    exact ⟨t,actual,⟨trace⟩,summary,
      fun i => ⟨.cons trace summary rfl .nil⟩⟩

/-- There must be an independently eligible direct head or a
literally addressed complete producer for every original input.
A different finite producer at an equal-denoting name is not evidence
for this original lower coordinate. -/
theorem no_actual_source_input_cannot_be_selected404 {s q d a}
    (arg : a ∈ q.demand.arguments)
    (noDirect : ¬ Nonempty (SourceArgument403 s a))
    (nothingComplete : ∀ need : OutputNeed s, Nonempty (LiteralInputNeed404 s a need) →
      ¬ Classifies supportedVariableSource404 s need.producer (.selected need.dictionary)) :
    ¬ Classifies supportedVariableSource404 s q (.selected d) := by
  intro chosen
  obtain ⟨t,e,⟨trace⟩,_,_⟩ := any_selected_producer_supports_its_original_outputs404 chosen
  obtain ⟨eligible⟩ := actual_classifies_input404 trace a arg
  cases eligible with
  | authored written => exact noDirect ⟨written⟩
  | output literal supporting _ _ =>
    exact no_finite_selected_producer_no_support404 (nothingComplete _ ⟨literal⟩) ⟨supporting⟩

/-- Corollary for the final concrete rule system even in the
presence of its native K2 and supported ambiguity alternatives. -/
theorem unfinished_exact_outputs_cannot_activate_original_input404 {s q d a}
    (arg : a ∈ q.demand.arguments) (noDirect : ¬ Nonempty (SourceArgument403 s a))
    (unfinished : ∀ need : OutputNeed s, Nonempty (LiteralInputNeed404 s a need) →
      ¬ Classifies completedChoiceSource404 s need.producer (.selected need.dictionary)) :
    ¬ Classifies completedChoiceSource404 s q (.selected d) := by
  intro chosen
  apply no_actual_source_input_cannot_be_selected404 arg noDirect ?_
    (completed_native_rejection_does_not_create_selections404.mp
      (completed_ambiguity_preserves_exact_selection404.mp chosen))
  intro need addressed completed
  exact unfinished need addressed (completed_ambiguity_preserves_exact_selection404.mpr
    (completed_native_rejection_does_not_create_selections404.mpr completed))

theorem only_wrong_target_outputs_cannot_activate_original_input404 {s q d a}
    (arg : a ∈ q.demand.arguments) (noDirect : ¬ Nonempty (SourceArgument403 s a))
    (misplaced : ∀ need : OutputNeed s,
      Classifies completedChoiceSource404 s need.producer (.selected need.dictionary) →
      need.expected.original.target ≠ a.lower) :
    ¬ Classifies completedChoiceSource404 s q (.selected d) := by
  apply unfinished_exact_outputs_cannot_activate_original_input404 arg noDirect
  exact fun need addressed done => wrong_target_is_not_direct_input_support404 (misplaced need done) addressed


/-- For this concrete classifier, a closed family whose one
required input per request depends on another member's output has no
finite selected proof. No member is assumed unfinished up front.
Ordinary raw equations may remain present. This induction is over
proof objects, not a termination claim about a resolution algorithm. -/
theorem closed_outputs_without_independent_base_cannot_select404
    {s : State} (family : Request → Prop)
    (internal : ∀ q, family q →
      ∃ a ∈ q.demand.arguments, ¬ Nonempty (SourceArgument403 s a) ∧
        ∀ need : OutputNeed s, Nonempty (LiteralInputNeed404 s a need) → family need.producer)
    {q d} (inside : family q) :
    ¬ Classifies completedChoiceSource404 s q (.selected d) := by
  rintro ⟨t,event,⟨trace⟩,summary⟩
  apply closed_source_family_cannot_complete family ?_ trace d summary inside
  intro current e needs elected member
  obtain ⟨a,original,noDirect,closed⟩ := internal current member
  rcases elected with old|new
  · obtain ⟨chosen⟩ := old.2.1
    exact (noDirect ⟨chosen.elected.scope.ready a original⟩).elim
  · obtain ⟨chosen⟩ := new.1
    cases chosen.choice.input a original with
    | authored direct => exact (noDirect ⟨direct⟩).elim
    | viaOutput slot found literal bounded =>
      exact .inl ⟨_,List.mem_of_getElem? found,closed _ ⟨literal⟩⟩

theorem final_raw_root_K2_is_independent_of_output_completion404 {s q}
    (raw : RootCycle s q) :
    Classifies completedChoiceSource404 s q .rejected ∧
      ∀ d, ¬ Classifies completedChoiceSource404 s q (.selected d) :=
  ⟨root_k2_is_rejected_for_every_primitive_system raw,fun _ => root_k2_never_selects raw⟩

end Yulang.GeneralDeclarativeI65.I72
