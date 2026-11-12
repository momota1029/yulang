import Yulang.GeneralNominalProjectionPropagation
import Yulang.GeneralNominalLocalBoundary
import Yulang.GeneralNominalRegressions
import Yulang.CommonBoundCoalescing

/-! Non-point descriptors and actual-occurrence sharing on the general shared
carrier. These tests exercise extraction and propagation, not a replacement
fragment classifier. The previous nominal candidate regressions are retained. -/
namespace Yulang.GeneralNominalIntervalExamples

open GeneralNominalProjections
open GeneralNominalProjectionPropagation
open CommonNominalFullCarrier

abbrev base : GeneralSourceState.State where
  slots := 4
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev descriptor : GeneralNominalState.Descriptor 4 :=
  ⟨0,⟨[.type],0⟩,[.type (2,3)],rfl⟩

abbrev source : GeneralNominalState.State where
  base := base
  view := view
  constructors := GeneralDeclarationExamples.constructors
  nominals := fun slot => if slot.val < 2 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · cases recorded
  bodies_opaque := by intro _ _ _; rfl

abbrev model (a b : Inference.Base) : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then nominal 0 [.inl (.base a)]
    else if identity = 1 then nominal 0 [.inl (.base b)]
    else if identity = 2 then .bottom else .top, Common.rowEmpty)

private theorem bottom_base (a : Inference.Base) : Subtype .bottom (.base a) :=
  (CommonNominalFullModelMap.subtype_exact _ _).mpr (CommonBoundCoalescing.bottom_le (.base a))

private theorem base_top (a : Inference.Base) : Subtype (.base a) .top :=
  (CommonNominalFullModelMap.subtype_exact _ _).mpr (CommonBoundCoalescing.le_top (.base a))

theorem source_models (a b : Inference.Base) : GeneralNominalState.Models source (model a b) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact PresenceNormalForm.all_nil _ _
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro slot d recorded
    have bounded : slot.val < 2 := by
      by_cases small : slot.val < 2
      · exact small
      · simp [source,small] at recorded
    have same : descriptor = d := by simpa [source,bounded] using recorded
    subst d
    have zeroOrOne : slot = 0 ∨ slot = 1 := by
      have : slot.val = 0 ∨ slot.val = 1 := by omega
      rcases this with zero | one
      · exact Or.inl (Fin.ext zero)
      · exact Or.inr (Fin.ext one)
    rcases zeroOrOne with rfl | rfl
    · exact ⟨[.inl (.base a)],.cons ⟨bottom_base a,base_top a⟩ .nil,
        subtype_refl _,subtype_refl _⟩
    · exact ⟨[.inl (.base b)],.cons ⟨bottom_base b,base_top b⟩ .nil,
        subtype_refl _,subtype_refl _⟩
  · exact PresenceNormalForm.all_nil _ _

abbrev first : Binding source := parameterBinding source 0 descriptor 0 7 (.type (2,3))
abbrev last : Binding source := parameterBinding source 1 descriptor 0 7 (.type (2,3))

theorem nonpoint_extract : extract source 0 descriptor 0 [[7]] descriptor.arguments = some [first] := rfl

theorem nonpoint_models (a b : Inference.Base) : Models ⟨source,[first]⟩ (model a b) := by
  have valid := parameter_binding_valid source (model a b) (source_models a b)
    0 descriptor rfl 0 7 (.type (2,3)) rfl
  exact ⟨source_models a b, single_capture_compatible _ _ _ valid⟩

theorem different_endpoints (a b : Inference.Base) :
    (2 : Fin 4) ≠ 3 ∧ (model a b 2).1 ≠ (model a b 3).1 := by
  exact ⟨by decide +kernel, by intro impossible; cases impossible⟩

theorem nonpoint_ordinary_propagation (a b : Inference.Base) :
    ∃ atoms, compile source [first] = some atoms ∧
      GeneralNominalState.Models (GeneralNominalState.extend source [] atoms) (model a b) := by
  obtain ⟨atoms,compiled,_⟩ := compile_sound source (model a b) [first] (nonpoint_models a b).2
  exact ⟨atoms,compiled, ((propagation_exact source (model a b) [first] atoms compiled).mpr
    (nonpoint_models a b)).1⟩

theorem coarse_checks_pass (a b : Inference.Base) :
    ∃ atoms, compile source [first,last] = some atoms ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model (model a b) atoms := by
  apply (compile_exact ..).mpr
  intro x hx y hy _
  have below : Subtype .bottom .top := subtype_trans (bottom_base a) (base_top a)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    exact ⟨below,below,below,below⟩

theorem coarse_actual_conflict : ¬ Models ⟨source,[first,last]⟩ (model .int .str) := by
  apply incompatible_occurrences_excluded _ _ first last
    (by simp) (by simp) rfl (.inl (.base .int)) (.inl (.base .str))
  · exact .argument (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
  · exact .argument (.source 1) ⟨subtype_refl _,subtype_refl _⟩ rfl
  · intro same
    have old : Common.Subtype (.base .int) (.base .str) :=
      (CommonNominalFullModelMap.subtype_exact _ _).mp same.1
    cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem row_checks_generated :
    GeneralNominalIntervalLaws.checks base (.row (0,1)) (.row (2,3)) =
      some [.rowLe (.var 0) (.var 1), .rowLe (.var 0) (.var 3),
        .rowLe (.var 2) (.var 1), .rowLe (.var 2) (.var 3)] := rfl

theorem index_pending_not_K2 :
    GeneralNominalState.RootPending GeneralNominalRegressions.indexState' GeneralSourceStateExamples.indexDemand ∧
      ¬ GeneralNominalK2Coverage.RootK2 GeneralNominalRegressions.indexState' GeneralSourceStateExamples.indexDemand :=
  ⟨GeneralNominalRegressions.index_pending,
    GeneralNominalK2Coverage.pending_excludes_K2 _ _ GeneralNominalRegressions.index_pending⟩

theorem loop_K2 : GeneralNominalK2Coverage.RootK2 GeneralNominalRegressions.loopState'
    GeneralSourceStateExamples.loopDemand :=
  GeneralNominalK2Coverage.old_rootK2 _ _ GeneralNominalRegressions.loop_K2

theorem shadow_not_K2 : ¬ GeneralNominalK2Coverage.RootK2 GeneralNominalRegressions.shadowState'
    GeneralSourceStateExamples.loopDemand :=
  GeneralNominalK2Coverage.pending_excludes_K2 _ _ GeneralNominalRegressions.shadow_pending

end Yulang.GeneralNominalIntervalExamples
