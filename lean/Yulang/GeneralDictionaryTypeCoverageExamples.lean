import Yulang.GeneralDictionaryTypeCoverage
import Yulang.GeneralNominalState

/-! Reservations and row coordinates are not actual type slots. These supplied
snapshots exercise localization only, without asserting a state-extension or
whole-materialization theorem. Repeated endpoint/output occurrences survive. -/
namespace Yulang.GeneralDictionaryTypeCoverageExamples
open GeneralSourceState (State Demand)
open GeneralDictionaryTypeCoverage
open GeneralDictionaryHeadlessLocations (locate)
open GeneralDictionaryBinderLocations (locateTerm)

private abbrev snapshot (slots : Nat) (source rowSource : Fin slots → Nat)
    (injective : Function.Injective source) : State where
  slots := slots
  source := source
  source_injective := injective
  rowSource := rowSource
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro first; exact Fin.elim0 first
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev beforeBase : State := snapshot 1 (fun _ => 10) (fun _ => 42)
  (by intro first last _; exact Subsingleton.elim first last)
abbrev afterBase : State := snapshot 2 (fun slot => if slot.val = 0 then 10 else 77)
  (fun slot => 42 + slot.val)
  (by
    intro first last same
    apply Fin.ext
    have firstBound := first.isLt
    have lastBound := last.isLt
    dsimp at same
    split at same <;> split at same <;> omega)

private def beforeView : GeneralNormalizedObservation.Snapshot beforeBase where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro first; exact Fin.elim0 first
  canonical := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev before : GeneralNominalState.State :=
  { GeneralNominalState.embed beforeBase beforeView (fun _ => none) with reserved := [77] }
abbrev roles : Roles.RoleDecls := fun _ => ⟨2, fun _ => some none, by
  intro _ _ impossible; cases impossible⟩
abbrev demand : Demand roles where
  role := 0
  arguments := fun _ => (77, 77)
  outputs := [⟨0, 77⟩, ⟨0, 77⟩]
  declared := by intro _ _; exact ⟨none, rfl⟩

/-- Mixed nominal linkage holds even though the demanded type ID is reserved only. -/
theorem reserved_linked : GeneralNominalState.Linked before demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources, before]
  · intro output member
    have same : output = ⟨0, 77⟩ := by simpa [demand] using member
    subst output
    simp [GeneralNominalState.sources, before]

theorem reserved_unavailable : locate before.base demand = none := by
  apply (locate_none_missing_iff _ _).mpr
  refine ⟨77, ?_, ?_⟩
  · simp [demandTypeIDs, demand]
  · intro slot
    change 10 ≠ 77
    decide

/-- A single coverage-list entry supplies every repeated occurrence. -/
theorem after_coverage : Covers afterBase [77] := by
  intro source member
  have same : source = 77 := List.mem_singleton.mp member
  subst source
  exact ⟨1, rfl⟩

def afterInputs : GeneralDictionaryVariableHeads.HeadlessInputs afterBase demand where
  lower := fun _ => 1
  upper := fun _ => 1
  target := fun _ => 1
  arguments := by intro _; rfl
  targets := by
    intro index
    obtain ⟨index, bound⟩ := index
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

theorem after_located : locate afterBase demand = some afterInputs := by
  obtain ⟨inputs, found⟩ := locate_of_coverage afterBase demand after_coverage
    (by intro source member; simpa [demandTypeIDs, demand] using member)
  rw [GeneralDictionaryHeadlessLocations.inputs_unique inputs afterInputs] at found
  exact found

/-- The computed vector retains two targets, even though both use the same slot. -/
theorem repeated_occurrences :
    demandTypeIDs demand = [77, 77, 77, 77, 77, 77] ∧
      List.ofFn afterInputs.lower = [1, 1] ∧
      List.ofFn afterInputs.upper = [1, 1] ∧
      List.ofFn afterInputs.target = [1, 1] := by decide +kernel

/-- An existing row ID is still not a type ID after the supplied enlargement. -/
theorem row_only_not_covered : afterBase.rowSource 0 = 42 ∧ ¬ Covers afterBase [42] := by
  refine ⟨rfl, ?_⟩
  intro covered
  obtain ⟨slot, impossible⟩ := covered 42 (by simp)
  change (if slot.val = 0 then 10 else 77) = 42 at impossible
  split at impossible <;> cases impossible

theorem variable_before_after :
    locateTerm before.base (.var 77) = none ∧
      locateTerm afterBase (.var 77) = some (.var 1) ∧
      locateTerm afterBase (.var 42) = none := by decide +kernel

end Yulang.GeneralDictionaryTypeCoverageExamples
