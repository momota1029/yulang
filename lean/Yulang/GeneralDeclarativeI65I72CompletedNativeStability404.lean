import Yulang.GeneralDeclarativeI65I72CompletedNative404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes)
open GeneralDeclarativeHead320 (Equation)

noncomputable def preserve_completed_lower_when_admitting_native404 {s q t event}
    (trace : SourceTrace supportedVariableSource404 s q t event) :
    SourceTrace completedNativePrioritySource404 s q t event :=
  SourceTrace.rec (R := supportedVariableSource404) (s := s)
    (motive_1 := fun q t e _ => SourceTrace completedNativePrioritySource404 s q t e)
    (motive_2 := fun qs ts _ => WhereForest completedNativePrioritySource404 s qs ts)
    (motive_3 := fun needs _ => SupportForest completedNativePrioritySource404 s needs)
    (fun cycle => .rootK2 cycle)
    (fun verdict safe old _ child => .other verdict safe (.inl old) child)
    (fun e safe rule _ _ support kids => .selected e safe rule support kids)
    .nil (fun _ _ first rest => .cons first rest)
    .nil (fun _ completed typed _ source rest => .cons source completed typed rest) trace

/-- Successful where children and actual producers have selected
summaries. Removing the added rejecting clause preserves the exact
successful source events, in the same State and original order. -/
theorem successful_matched_source_same_before_native404 {s q t event}
    (trace : SourceTrace completedNativePrioritySource404 s q t event) :
    ∀ d, Summarizes t (.selected d) →
      Nonempty (SourceTrace supportedVariableSource404 s q t event) := by
  exact SourceTrace.rec (R := completedNativePrioritySource404) (s := s)
    (motive_1 := fun q t event _ => ∀ d, Summarizes t (.selected d) →
      Nonempty (SourceTrace supportedVariableSource404 s q t event))
    (motive_2 := fun qs ts _ => ∀ ds : List Dictionary, All₂ Summarizes ts (ds.map Result.selected) →
      Nonempty (WhereForest supportedVariableSource404 s qs ts))
    (motive_3 := fun needs _ => Nonempty (SupportForest supportedVariableSource404 s needs))
    (fun _ _ proves => by cases proves)
    (fun verdict _ _ _ _ _ proves => by cases verdict <;> cases proves)
    (fun e safe chose _ _ recSupport recChildren _ summary => by
      cases summary with
      | selected localChildren merged =>
        cases merged with
        | selected same =>
          rw [same] at localChildren
          obtain ⟨support⟩ := recSupport
          obtain ⟨children⟩ := recChildren _ localChildren
          exact ⟨.selected e safe chose support children⟩)
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

theorem completed_native_rejection_does_not_create_selections404 {s q d} :
    Classifies completedNativePrioritySource404 s q (.selected d) ↔
      Classifies supportedVariableSource404 s q (.selected d) := by
  constructor
  · rintro ⟨t,event,⟨trace⟩,summary⟩
    exact ⟨t,event,successful_matched_source_same_before_native404 trace d summary,summary⟩
  · rintro ⟨t,event,⟨trace⟩,summary⟩
    exact ⟨t,event,⟨preserve_completed_lower_when_admitting_native404 trace⟩,summary⟩

theorem completed_native_priority_dictionary_sound404 : DictionarySound completedNativePrioritySource404 :=
  fun s q d chosen m fit => completed_input_dictionary_sound404 s q d
    (completed_native_rejection_does_not_create_selections404.mp chosen) m fit

noncomputable def genuine_producer_opens_native_child404 {s q t e dict}
    (source : SourceTrace variableWithNativeK2403 s q t (some e))
    (completed : Summarizes t (.selected dict)) (i : Fin q.demand.outputs.length) :
    SupportForest completedNativePrioritySource404 s [needOfSelected404 e dict i] :=
  .cons (preserve_completed_lower_when_admitting_native404 (preserve_c403_derivation404 source))
    completed rfl .nil

theorem completed_outer_and_pending_inner_k2404 {s producer consumer t e dict row}
    (source : SourceTrace variableWithNativeK2403 s producer t (some e))
    (completed : Summarizes t (.selected dict)) (i : Fin producer.demand.outputs.length)
    (entry : CompletedUnaryEntry404 s consumer row (needOfSelected404 e dict i))
    {done : Nat → Prop} (origins : GeneralDeclarativeOrigins321.Supported s.core.current.ordinary done)
    (tag owner : Nat)
    (observed : origins.derivesFrom
      (⟨entry.lowerChild,.nominal tag [.variable entry.lowerChild]⟩ : Equation) (.output owner))
    (onlyPending : ∀ o, origins.derivesFrom
      (⟨entry.lowerChild,.nominal tag [.variable entry.lowerChild]⟩ : Equation) o →
        ∃ n, o = .output n ∧ ¬ done n) :
    (⟨entry.lowerChild,.nominal tag [.variable entry.lowerChild]⟩ : Equation)
      ∉ (GeneralDeclarativeOrigins321.restriction origins).equations ∧
      Classifies completedNativePrioritySource404 s consumer .rejected := by
  refine ⟨GeneralDeclarativeOrigins321.pending_only origins _ onlyPending,?_⟩
  let opened := genuine_producer_opens_native_child404 source completed i
  have raw := GeneralDeclarativeK2Alias321.cycle_in_alias_graph
    (GeneralDeclarativeGraphRows321.pending_nominal_self_cycle origins owner observed)
  exact (actual_completed_native_child_k2_rejects404
    ⟨needOfSelected404 e dict i,0,rfl,row,entry,raw⟩ opened).1

end Yulang.GeneralDeclarativeI65.I72
