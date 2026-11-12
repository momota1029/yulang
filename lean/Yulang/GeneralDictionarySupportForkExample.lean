import Yulang.GeneralDictionarySupportEvidence
import Yulang.GeneralNominalReobservationExamples

/-! An inhabited stable selected support state obtained by certified refresh.
This is a concrete, packet-free terminal evidence instance, not a general V5 bridge. -/
namespace Yulang.GeneralDictionarySupportForkExample
open GeneralNominalRefreshFork GeneralNominalSupport GeneralNominalSaturationState
open GeneralSourceDictionaries GeneralDeclarations
open GeneralDeclarationExamples (roles)

abbrev start : Tracked roles := GeneralNominalSupport.initial (context none) root
abbrev refreshed (wide : Bool) : Tracked roles := { start with current := after wide }

theorem refresh_step (wide : Bool) : GeneralNominalSupportSteps.Step registry root start (refreshed wide) :=
  ⟨root,.root,.administrative root _ (.refresh root (context (some wide)) (certificate wide) 0
    (by simp only [GeneralNominalState.sources,List.mem_append,List.mem_ofFn]; exact Or.inl (Or.inl (Or.inl ⟨⟨0,by decide +kernel⟩,rfl⟩)))
    (fun known => initial_pending.choose_spec known) (zero_known wide))⟩

theorem repair_step : GeneralNominalSupportSteps.Step registry root (refreshed true) (refreshed false) :=
  ⟨root,.root,.administrative root _ (.reobserve root GeneralNominalReobservationExamples.revision
    GeneralNominalReobservationExamples.revision_certified GeneralNominalReobservationExamples.revision_improves)⟩

theorem reachable (wide : Bool) : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles)
    registry root (refreshed wide) := ⟨start,⟨context none,initial_source,rfl⟩,.tail .refl (refresh_step wide)⟩

theorem point_stable : GeneralNominalSupportSteps.Stable registry (refreshed false) root := by
  intro focus generated next update
  exact GeneralNominalReobservationExamples.point_stable focus generated next.current
    (GeneralNominalSupportSteps.at_old update)

theorem wide_not_stable : ¬ GeneralNominalSupportSteps.Stable registry (refreshed true) root := by
  intro stable
  obtain ⟨focus,generated,update⟩ := repair_step
  exact stable focus generated _ update

private theorem ready (slot : Fin 5) (test : GeneralNominalRecursiveInspection.Test)
    (observation : GeneralCanonicalObservations.Observation)
    (head : Head (state (some false)) slot.val test observation) :
    ReadyAt (refreshed false) [] slot.val := by
  refine ⟨test,observation,head,state (some false),observation,head,?_⟩
  intro valuation valid
  exact GeneralCanonicalObservations.recorded_sound _ valuation
    (refresh_models_forward false valuation valid.1) (head_recorded head)

private theorem root_ready : Roots (refreshed false) [] root := by
  intro index
  exact ready 0 _ _ (.nominal (snapshot := state (some false)) 0 (descriptor (2,2)) rfl)

theorem decisions : DecisionGuard (refreshed false) registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),root_ready,?_⟩
  intro decl member role bounds located slot inspected
  have same := List.mem_singleton.mp member
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (GeneralNominalRefreshForkClassification.located (some false)))
  subst bounds
  have read_exact : readsMany (state (some false))
      (GeneralNominalInspection.queries (state (some false)) (context (some false)).interpretation declaration)
      [(0,0)] = [(0 : Fin 5),2,3] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      readsMany,GeneralNominalSupport.reads,GeneralNominalRecursiveInspection.typeArguments,state,view]
    change readsMany (state (some false)) [.nominal 0 [.scalar .int]] [(2,2)] = [2,3]
    simp [readsMany,GeneralNominalSupport.reads,GeneralNominalRecursiveInspection.typeArguments,state]
    change readsMany (state (some false)) [.scalar .int] [(3,3)] = [3]
    simp [readsMany,GeneralNominalSupport.reads]
  change slot ∈ readsMany (state (some false))
      (GeneralNominalInspection.queries (state (some false)) (context (some false)).interpretation declaration) [(0,0)] at inspected
  rw [read_exact] at inspected
  change (slot : Fin 5) ∈ [(0 : Fin 5),2,3] at inspected
  have alternatives : slot = (0 : Fin 5) ∨ slot = (2 : Fin 5) ∨ slot = (3 : Fin 5) := by
    rcases List.mem_cons.mp inspected with first | rest
    · exact Or.inl first
    · rcases List.mem_cons.mp rest with second | last
      · exact Or.inr (Or.inl second)
      · exact Or.inr (Or.inr (List.mem_singleton.mp last))
  rcases alternatives with zero | two | three
  · have equal : slot = (0 : Fin 5) := zero
    subst slot
    exact ready 0 _ _ (.nominal (snapshot := state (some false)) 0 (descriptor (2,2)) rfl)
  · subst slot
    exact ready 2 _ _ (.nominal (snapshot := state (some false)) 2 (descriptor (3,3)) rfl)
  · subst slot
    exact ready 3 _ _ (.scalar (snapshot := state (some false)) 3 .int rfl)

theorem point_selected : GeneralNominalSupportBoundary.Local registry (refreshed false) root (.selected 90 []) :=
  GeneralNominalSupportBoundary.selected_supported GeneralNominalRefreshDivergence.point_selected [] decisions

theorem terminal_evidence : GeneralDictionaryRecursiveEvidence.Evidence registry (refreshed false).current.context
    model root (.node 90 []) :=
  (GeneralDictionarySupportEvidence.reachable_packetFree_terminal registry root root (refreshed false)
    (reachable false) rfl (Or.inl rfl) 90 [] point_stable point_selected).2 model (after_models false)

/-- The generic packet-free evidence theorem has an inhabited, actually reachable,
stable selected instance after source-entailed observation recovery. -/
theorem inhabited_terminal :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root (refreshed false) ∧
    GeneralNominalSupportSteps.Stable registry (refreshed false) root ∧
    GeneralNominalSupportBoundary.Local registry (refreshed false) root (.selected 90 []) ∧
    (refreshed false).current.packets = [] ∧ Models (refreshed false).current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry (refreshed false).current.context model root (.node 90 []) :=
  ⟨reachable false,point_stable,point_selected,rfl,after_models false,terminal_evidence⟩

end Yulang.GeneralDictionarySupportForkExample
