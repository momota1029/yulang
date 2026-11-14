import Yulang.GeneralNominalCenteredFixedChoice
import Yulang.GeneralNominalCenteredSelectionCounterexample

/-! A concrete reorder changes the literal terminal-state predicate. This
does not identify the final Local observations of the fixed chooser. -/
namespace Yulang.GeneralNominalCenteredExitPredicates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal GeneralNominalCenteredFixedChoice
open GeneralNominalCenteredRegistryJournal
open GeneralNominalCenteredSelectionCounterexample
open GeneralDictionaryEarlyMergeScalarExample (registry declaration packet registry_checked source)
open GeneralNominalExamples (displayRoot context intDisplay)
open GeneralDeclarationExamples (roles constructors)

def reordered : Registry := ⟨constructors,roles,[intDisplay,declaration]⟩

theorem order : GeneralRegistryReordering.Reorders registry reordered :=
  ⟨rfl,rfl,[intDisplay,declaration],List.Perm.swap ..,
    .cons (GeneralRegistryReordering.declarationReorders_refl _)
      (.cons (GeneralRegistryReordering.declarationReorders_refl _) .nil)⟩

theorem distinct : registry ≠ reordered := by
  intro same
  have ids := congrArg (fun registry : Registry => registry.declarations.map Declaration.id) same
  change [1,3] = [3,1] at ids
  cases ids

theorem reordered_checked : (boundary roles).Checked reordered :=
  ⟨rfl,GeneralRegistryReordering.reorders_checked order registry_checked⟩

theorem start_initial : (boundary roles).Initial registry displayRoot cstart :=
  ⟨context true,[.app 0 [.app 2 []]],source,(fun _ => rfl),
    GeneralNominalCenteredPointMergeExample.ground,rfl⟩

theorem start_reachable : B4TargetV5.Reachable (boundary roles) registry displayRoot cstart :=
  ⟨cstart,start_initial,.refl⟩

theorem reordered_start_reachable : B4TargetV5.Reachable (boundary roles) reordered displayRoot cstart :=
  ⟨cstart,GeneralNominalCenteredAdministrativeComposition.initialReorders registry reordered
    ⟨rfl,registry_checked⟩ reordered_checked order cstart displayRoot start_initial,.refl⟩

private theorem append_steps (first : B4Target.Steps relation start middle)
    (last : B4Target.Steps relation middle finish) : B4Target.Steps relation start finish := by
  induction last with
  | refl => exact first
  | tail prior step ih => exact .tail ih step

theorem exit_difference : ∃ final, Exit registry cstart displayRoot final ∧
    ¬ Exit reordered cstart displayRoot final := by
  obtain ⟨final,path,stopped⟩ := exit_exists ⟨rfl,registry_checked⟩ ground_reachable
  have recorded : packet ∈ final.erased.current.packets :=
    packet_steps path (List.mem_cons_self ..)
  refine ⟨final,⟨append_steps (.tail .refl cfirst) path,stopped⟩,?_⟩
  rintro ⟨otherPath,_⟩
  have tagged := registry_reachable
    (B4TargetV5.reachable_steps (boundary roles) reordered_start_reachable otherPath) packet recorded
  exact distinct tagged

theorem exit_predicates_not_equal :
    Exit registry cstart displayRoot ≠ Exit reordered cstart displayRoot := by
  obtain ⟨final,one,two⟩ := exit_difference
  intro same
  exact two (same ▸ one)

theorem inhabited_distinct_exit_predicates :
    GeneralRegistryReordering.Reorders registry reordered ∧ registry ≠ reordered ∧
    (boundary roles).Checked registry ∧ (boundary roles).Checked reordered ∧
    B4TargetV5.Reachable (boundary roles) registry displayRoot cstart ∧
    B4TargetV5.Reachable (boundary roles) reordered displayRoot cstart ∧
    (∃ final, Exit registry cstart displayRoot final) ∧
    (∃ final, Exit reordered cstart displayRoot final) ∧
    Exit registry cstart displayRoot ≠ Exit reordered cstart displayRoot :=
  ⟨order,distinct,⟨rfl,registry_checked⟩,reordered_checked,start_reachable,reordered_start_reachable,
    exit_exists ⟨rfl,registry_checked⟩ start_reachable,
    exit_exists reordered_checked reordered_start_reachable,exit_predicates_not_equal⟩

end Yulang.GeneralNominalCenteredExitPredicates
