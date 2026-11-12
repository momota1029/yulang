import Yulang.GeneralDictionaryInspectionLocality
import Yulang.GeneralDictionaryRefreshDescriptors

/-! Finished flat nominal inspection survives actual same-carrier descriptor
refinement with a fixed normalized view. No footprint assumption is required. -/
namespace Yulang.GeneralDictionaryFinishedRefresh
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality
open GeneralDictionaryRefreshDescriptors

theorem finished_nominal_lower (state : GeneralNominalState.State) (name : Nat)
    (patterns : List Query) (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name patterns) bounds origin)) :
    ∃ descriptor, state.nominals bounds.1 = some descriptor := by
  cases found : state.nominals bounds.1 with
  | some descriptor => exact ⟨descriptor,rfl⟩
  | none =>
    simp only [inspect,found] at finished
    cases head : state.view.heads bounds.1 <;>
      simp_all [Finished,Report.visit,block]

theorem finished_nominal_upper (state : GeneralNominalState.State) (name : Nat)
    (patterns : List Query) (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name patterns) bounds origin)) :
    ∃ descriptor, state.nominals bounds.2 = some descriptor := by
  obtain ⟨lower,found⟩ := finished_nominal_lower state name patterns bounds origin finished
  by_cases equal : bounds.1 = bounds.2
  · exact ⟨lower,equal ▸ found⟩
  cases upper : state.nominals bounds.2 with
  | some descriptor => exact ⟨descriptor,rfl⟩
  | none =>
    simp only [inspect,found,equal,ite_false,upper] at finished
    split at finished
    · split at finished <;> simp_all [Finished,Report.visit,block]
    · simp_all [Finished,Report.visit]

theorem variable_footprints (state : GeneralNominalState.State)
    (groups : List (List Nat)) (bounds : List (Bounds state)) :
    footprints state (groups.map Query.variables) bounds = [] := by
  induction groups generalizing bounds with
  | nil => cases bounds <;> simp [footprints]
  | cons group groups ih => cases bounds <;> simp [footprints,ih]

theorem flat_nominal_footprint (state : GeneralNominalState.State) (name : Nat)
    (groups : List (List Nat)) (bounds : Bounds state) :
    footprint state (.nominal name (groups.map Query.variables)) bounds = [bounds.1,bounds.2] := by
  simp only [footprint]
  repeat' split
  all_goals simp [variable_footprints]

theorem flat_nominal_finished_preserved (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (name : Nat) (groups : List (List Nat)) (bounds : Bounds context.state) (origin : Option Origin)
    (finished : Finished (inspect context.state (.nominal name (groups.map Query.variables)) bounds origin)) :
    inspect (reobserve context next).state (.nominal name (groups.map Query.variables)) bounds origin =
      transferReport context next (inspect context.state (.nominal name (groups.map Query.variables)) bounds origin) := by
  apply inspect_local context next view
  intro slot member
  rw [flat_nominal_footprint] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  obtain ⟨lower,low⟩ := finished_nominal_lower context.state name _ bounds origin finished
  obtain ⟨upper,high⟩ := finished_nominal_upper context.state name _ bounds origin finished
  rcases member with same | same
  · subst slot
    exact (descriptor_preserved context next refinement bounds.1 lower low).trans low.symm
  · subst slot
    exact (descriptor_preserved context next refinement bounds.2 upper high).trans high.symm

end Yulang.GeneralDictionaryFinishedRefresh
