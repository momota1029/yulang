import Yulang.GeneralDictionaryUnaryCurrentEvidence

/-! Actual demand lookup is transported by source-preserving refinements.
Successful old lookup is sufficient; failed lookup need not be preserved. -/
namespace Yulang.GeneralDictionaryRefinedLocations
open GeneralSourceState GeneralDictionaryBinderLocations

theorem source_slot (before after : State) (refinement : Refines before after)
    (source : Nat) (slot : Fin before.slots) (found : sourceSlot before source = some slot) :
    sourceSlot after source = some (refinement.embed slot) :=
  (sourceSlot_exact after source _).mpr ((refinement.source slot).trans
    ((sourceSlot_exact before source slot).mp found))

theorem locate_cons (state : State) (first : Interval) (rest : List Interval) :
    GeneralCandidateBoundaryParts.locate state (first::rest) =
      (sourceSlot state first.1).bind (fun lower => (sourceSlot state first.2).bind (fun upper =>
        (GeneralCandidateBoundaryParts.locate state rest).map (fun tail => (lower,upper)::tail))) := by
  simp only [GeneralCandidateBoundaryParts.locate,List.mapM_cons]
  cases sourceSlot state first.1 <;> cases sourceSlot state first.2 <;> simp only [Option.bind_none,Option.bind_some]
  all_goals try rfl
  change (GeneralCandidateBoundaryParts.locate state rest).bind (fun tail => some ((_,_)::tail)) = (GeneralCandidateBoundaryParts.locate state rest).map (fun tail => (_,_)::tail)
  cases GeneralCandidateBoundaryParts.locate state rest <;> rfl

theorem locate (before after : State) (refinement : Refines before after)
    (sources : List Interval) (bounds : List (Fin before.slots × Fin before.slots))
    (found : GeneralCandidateBoundaryParts.locate before sources = some bounds) :
    GeneralCandidateBoundaryParts.locate after sources =
      some (bounds.map fun b => (refinement.embed b.1,refinement.embed b.2)) := by
  induction sources generalizing bounds with
  | nil => have empty : bounds = [] := by simpa [GeneralCandidateBoundaryParts.locate] using found.symm
           subst bounds; rfl
  | cons first rest ih =>
    rw [locate_cons] at found ⊢
    cases low : sourceSlot before first.1 with
    | none => simp [low] at found
    | some lower =>
      cases high : sourceSlot before first.2 with
      | none => simp [low,high] at found
      | some upper =>
        cases tail : GeneralCandidateBoundaryParts.locate before rest with
        | none => simp [low,high,tail] at found
        | some remaining =>
          have original : bounds = (lower,upper)::remaining := by simpa [low,high,tail] using found.symm
          subst bounds
          rw [source_slot before after refinement _ _ low,source_slot before after refinement _ _ high]
          simp [ih remaining tail]

theorem arguments (before after : GeneralNominalRecursiveCandidates.Context)
    (refinement : GeneralNominalRefinements.Refines before.state after.state)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (bounds : List (GeneralNominalInspection.Bounds before.state))
    (found : GeneralNominalRecursiveCandidates.arguments before root = some bounds) :
    GeneralNominalRecursiveCandidates.arguments after root =
      some (bounds.map fun b => (refinement.base.embed b.1,refinement.base.embed b.2)) :=
  locate before.state.base after.state.base refinement.base _ bounds found

theorem metadata (before after : GeneralNominalRecursiveCandidates.Context)
    (refinement : GeneralNominalRefinements.Refines before.state after.state)
    (interpretation : after.interpretation = before.interpretation)
    (registry : GeneralDeclarations.Registry)
    (metadata : GeneralNominalRecursiveCandidates.Metadata registry before) :
    GeneralNominalRecursiveCandidates.Metadata registry after := by
  unfold GeneralNominalRecursiveCandidates.Metadata GeneralNominalCandidates.Metadata at *
  rw [refinement.constructors,interpretation]
  exact metadata
end Yulang.GeneralDictionaryRefinedLocations
