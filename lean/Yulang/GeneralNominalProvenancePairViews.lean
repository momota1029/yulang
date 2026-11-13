import Yulang.GeneralNominalProvenancePair
import Yulang.GeneralNominalValueObservation

/-! The representative paired journal remains unsupported after every
certified observation-only update. This is not a reachability certificate for
the distinct compound frames emitted by P. -/
namespace Yulang.GeneralNominalProvenancePairViews
open GeneralNominalProvenanceDeclarations GeneralNominalProvenanceSource
open GeneralNominalProvenancePair GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralNominalSupport GeneralNominalValueSupport GeneralNominalValueDepth
open GeneralNominalBudgetObservation

theorem view_sources (view : View before after) :
    ∀ identity ∈ GeneralNominalState.sources before.context.state,
      identity ∈ GeneralNominalState.sources after.context.state := by
  induction view with
  | current => exact fun _ member => member
  | refresh _ certificate ih =>
    exact fun identity member => GeneralNominalRefinements.sources certificate.refines identity (ih identity member)
  | reobserve revision _ certificate ih => exact ih

noncomputable abbrev observed (after : State roles) : Tracked roles := {journal with current := after}

theorem no_discharged_view (view : View journal.current after) (focus : Occurrence roles) :
    ¬ Discharged after focus :=
  fun done => no_discharged focus (discharge_transport (view_journal view).symm done)

theorem nominal_path (view : View journal.current after)
    (path : GeneralNominalFeedbackK2.Path journal.current first last) :
    GeneralNominalFeedbackK2.Path after first last := by
  induction path with
  | nil source => exact .nil source
  | cons edge rest ih =>
    refine .cons ⟨view_sources view _ edge.1,view_sources view _ edge.2.1,?_⟩ ih
    rcases edge.2.2 with structural | argument
    · obtain ⟨parent,child,⟨kind,_,_,_⟩,_,_⟩ := structural
      exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.argument_model_restriction
        (fun model valid => (GeneralNominalDownstreamSupport.view_models view model).mp valid) argument)

theorem pair_not_grounded_view (view : View journal.current after) :
    ¬ Grounded registry (observed after) wRoot ∧ ¬ Grounded registry (observed after) gRoot := by
  apply mutual_value_trap registry (observed after) wRoot gRoot
  · intro producer _
    exact no_discharged_view view producer
  · intro producer member
    rcases member with rfl | rfl
    · refine ⟨cRoot,waiting_transport (view_journal view) w_c_waiting,no_discharged_view view cRoot,
        5,.nominal 0 1,?_,?_⟩
      · exact .value (GeneralNominalValueObservation.proper_transport (view_journal view) w_c_proper)
          after .current (0 : Fin 2) (nominal_path view c_to_b) (.nominal 0 1) b_available
      · intro support head
        exact ⟨gRoot,b_necessary support head,Or.inr rfl⟩
    · refine ⟨dRoot,waiting_transport (view_journal view) g_d_waiting,no_discharged_view view dRoot,
        2,.nominal 0 1,?_,?_⟩
      · exact .value (GeneralNominalValueObservation.proper_transport (view_journal view) g_d_proper)
          after .current (0 : Fin 2) (nominal_path view d_to_a) (.nominal 0 1) a_available
      · intro support head
        exact ⟨wRoot,a_necessary support head,Or.inl rfl⟩

theorem a_blocked_view (view : View journal.current after) (support : List (Occurrence roles))
    (allowed : Supported registry (observed after) support) :
    ¬ HeadSupported (observed after) support 2 (.nominal 0 1) :=
  fun head => (pair_not_grounded_view view).1 (allowed wRoot (a_necessary support head))

theorem b_blocked_view (view : View journal.current after) (support : List (Occurrence roles))
    (allowed : Supported registry (observed after) support) :
    ¬ HeadSupported (observed after) support 5 (.nominal 0 1) :=
  fun head => (pair_not_grounded_view view).2 (allowed gRoot (b_necessary support head))

theorem no_head_depth (view : View journal.current after) (depth : Nat) :
    ¬ HeadDepth registry (observed after) depth 2 (.nominal 0 1) ∧
    ¬ HeadDepth registry (observed after) depth 5 (.nominal 0 1) := by
  constructor
  · rintro ⟨support,head,bounded⟩
    exact a_blocked_view view support (fun producer member => depth_grounded (bounded producer member)) head
  · rintro ⟨support,head,bounded⟩
    exact b_blocked_view view support (fun producer member => depth_grounded (bounded producer member)) head

/-- Inspection permission cannot use either entailed subterm head, even after
all cached observations allowed by View have been supplied. -/
theorem no_supported_needed_head (view : View journal.current after) :
    ¬ ∃ support, Supported registry (observed after) support ∧
      (HeadSupported (observed after) support 2 (.nominal 0 1) ∨
       HeadSupported (observed after) support 5 (.nominal 0 1)) := by
  rintro ⟨support,allowed,one | two⟩
  · exact a_blocked_view view support allowed one
  · exact b_blocked_view view support allowed two

end Yulang.GeneralNominalProvenancePairViews
