import Yulang.GeneralNominalRefinementTrace197

/-! Successful nominal observations survive arbitrary source-preserving slot
embeddings, including growth. Bounds are renamed; source-based origins are not. -/
namespace Yulang.GeneralNominalSlotObservation198
open GeneralNominalState (State Parameter)
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection (typeArguments)
open GeneralNominalRefinements (Refines renameParameter renameDescriptor)
open GeneralNominalRefinementTrace197 (Observed ObservedMany)

def bounds (embed : Fin first → Fin last) (pair : Fin first × Fin first) :=
  (embed pair.1,embed pair.2)

theorem embed_injective (refinement : Refines before after) : Function.Injective refinement.base.embed := by
  intro first last equal
  apply before.base.source_injective
  rw [← refinement.base.source first,← refinement.base.source last,equal]

theorem typeArguments_rename (embed : Fin first → Fin last) (parameters : List (Parameter first)) :
    typeArguments (parameters.map (renameParameter embed)) =
      (typeArguments parameters).map (List.map (bounds embed)) := by
  induction parameters with
  | nil => rfl
  | cons parameter parameters ih =>
    cases parameter with
    | row pair => rfl
    | type pair =>
      simp only [List.map_cons,typeArguments,List.mapM_cons,renameParameter]
      change (typeArguments (parameters.map (renameParameter embed))).bind
        (fun tail => some (bounds embed pair :: tail)) =
        ((typeArguments parameters).bind (fun tail => some (pair :: tail))).map (List.map (bounds embed))
      rw [ih]
      cases typeArguments parameters <;> rfl


theorem typeArguments_rename_some (embed : Fin first → Fin last)
    (found : typeArguments parameters = some pairs) :
    typeArguments (parameters.map (renameParameter embed)) = some (pairs.map (bounds embed)) := by
  rw [typeArguments_rename,found]
  rfl

mutual
  theorem observed (refinement : Refines before after) (source : Observed before query pair) :
      Observed after query (bounds refinement.base.embed pair) := by
    cases source with
    | variables => exact .variables
    | point recorded name arguments children =>
      apply Observed.point (refinement.nominals _ _ recorded) name
      · dsimp only [renameDescriptor]
        rw [typeArguments_rename,arguments]
        rfl
      · exact observedMany refinement children
    | interval different lower upper lowerName upperName lowerArgs upperArgs left right =>
      refine .interval (fun same => different (embed_injective refinement same))
        (refinement.nominals _ _ lower) (refinement.nominals _ _ upper) lowerName upperName ?_ ?_
        (observedMany refinement left) (observedMany refinement right)
      · dsimp only [renameDescriptor]
        rw [typeArguments_rename,lowerArgs]
        rfl
      · dsimp only [renameDescriptor]
        rw [typeArguments_rename,upperArgs]
        rfl
  termination_by sizeOf query
  theorem observedMany (refinement : Refines before after) (source : ObservedMany before queries pairs) :
      ObservedMany after queries (pairs.map (bounds refinement.base.embed)) := by
    cases source with
    | nil => exact .nil
    | cons first rest => exact .cons (observed refinement first) (observedMany refinement rest)
  termination_by sizeOf queries
end
end Yulang.GeneralNominalSlotObservation198
