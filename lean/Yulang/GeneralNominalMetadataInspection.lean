import Yulang.GeneralNominalMetadataEquivalence

/-! Inspection reads and recorded heads ignore ownership-list enumeration. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalMetadataInspection
open GeneralNominalMetadataEquivalence
open GeneralNominalInspection (Query Bounds)
open GeneralNominalSupport

variable (state : GeneralNominalState.State)
    (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem head (identity test observation) :
    Head (replace state allocated reserved) identity test observation ↔ Head state identity test observation := by
  constructor <;> intro seen <;> cases seen with
  | scalar _ _ recorded => exact .scalar _ _ recorded
  | structural _ _ _ recorded => exact .structural _ _ _ recorded
  | nominal _ _ recorded => exact .nominal _ _ recorded

mutual
  theorem reads (query : Query) (bounds : Bounds state) :
      GeneralNominalSupport.reads (replace state allocated reserved) query bounds =
        GeneralNominalSupport.reads state query bounds := by
    cases query with
    | variables | deferred | scalar => simp only [GeneralNominalSupport.reads]
    | node expected patterns =>
      simp only [GeneralNominalSupport.reads,replace]
      split
      · rfl
      · split
        · split
          · exact congrArg (fun xs => [bounds.1,bounds.2] ++ xs) (readsMany patterns _) 
          · rfl
        · rfl
    | nominal expected patterns =>
      simp only [GeneralNominalSupport.reads,replace]
      split
      · rfl
      · split
        · split
          · rfl
          · split
            · exact congrArg (List.cons bounds.1) (readsMany patterns _)
            · split
              · rfl
              · split
                · split
                  · rfl
                  · exact congrArg (fun xs => bounds.1 :: bounds.2 :: xs)
                      (congr (congrArg List.append (readsMany patterns _)) (readsMany patterns _))
                · rfl
        · rfl
    termination_by sizeOf query
  theorem readsMany (queries : List Query) (bounds : List (Bounds state)) :
      GeneralNominalSupport.readsMany (replace state allocated reserved) queries bounds =
        GeneralNominalSupport.readsMany state queries bounds := by
    cases queries with
    | nil => cases bounds <;> simp only [GeneralNominalSupport.readsMany]
    | cons query rest =>
      cases bounds with
      | nil => simp only [GeneralNominalSupport.readsMany]
      | cons bounds tail =>
        simp only [GeneralNominalSupport.readsMany,reads query bounds,
          readsMany rest tail]
    termination_by sizeOf queries
end

theorem queries (interpretation declaration) :
    GeneralNominalInspection.queries (replace state allocated reserved) interpretation declaration =
      GeneralNominalInspection.queries state interpretation declaration := rfl

theorem arguments (interpretation) (root : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalRecursiveCandidates.arguments ⟨replace state allocated reserved,interpretation⟩ root =
      GeneralNominalRecursiveCandidates.arguments ⟨state,interpretation⟩ root := rfl

end Yulang.GeneralNominalMetadataInspection
