import Yulang.GeneralDeclarativeI65I74PlainMergedLocation416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeGraphRows321 (structural observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

def withRedundantRead (s : GeneralDeclarativeHead320.State) (root : Nat) : GeneralDeclarativeHead320.State :=
  {s with equations := s.equations ++ [idempotentRow root]}

theorem a_redundant_read_never_changes_model_solutions416 (s : GeneralDeclarativeHead320.State) (root : Nat)
    (m : GeneralNominalCommonBridge.Assignment) :
    Models (withRedundantRead s root) m ↔ Models s m := by
  constructor
  · intro fit
    exact ⟨fit.1,fun row h => fit.2 row (List.mem_append_left _ h)⟩
  · intro fit
    refine ⟨fit.1,?_⟩
    intro row seen
    rcases List.mem_append.mp seen with old|new
    · exact fit.2 row old
    · cases List.mem_singleton.mp new
      exact self_join_is_semantically_idempotent416 (m root).1

private theorem variable_row_not_introduced416 {s : GeneralDeclarativeHead320.State} {root x y : Nat}
    (h : (⟨x,.variable y⟩ : Equation) ∈ (withRedundantRead s root).equations) :
    (⟨x,.variable y⟩ : Equation) ∈ s.equations := by
  rcases List.mem_append.mp h with old|fake
  · exact old
  · have mismatch := (Equation.mk.inj (List.mem_singleton.mp fake)).2
    cases mismatch

theorem a_redundant_read_preserves_actual_raw_alias416 (s : GeneralDeclarativeHead320.State) (root x y : Nat) :
    GeneralDeclarativeLowerKnown321.Alias (withRedundantRead s root) x y ↔ GeneralDeclarativeLowerKnown321.Alias s x y := by
  constructor
  · intro addr
    induction addr with
    | bounds lower upper => exact .bounds lower upper
    | forward row => exact .forward (variable_row_not_introduced416 row)
    | backward row => exact .backward (variable_row_not_introduced416 row)
    | trans _ _ l r => exact .trans l r
  · intro addr
    induction addr with
    | bounds lower upper => exact .bounds lower upper
    | forward row => exact .forward (List.mem_append_left _ row)
    | backward row => exact .backward (List.mem_append_left _ row)
    | trans _ _ l r => exact .trans l r

theorem a_redundant_read_preserves_raw_observation416 (s : GeneralDeclarativeHead320.State) (root x : Nat)
    (shape : GeneralDeclarativeK2Graph321.Shape) :
    observed (withRedundantRead s root) x shape ↔ observed s x shape := by
  constructor
  · rintro ⟨expr,row,decode⟩
    rcases List.mem_append.mp row with old|new
    · exact ⟨expr,old,decode⟩
    · have rhs := (Equation.mk.inj (List.mem_singleton.mp new)).2
      rw [rhs] at decode
      cases decode
  · rintro ⟨expr,row,decode⟩
    exact ⟨expr,List.mem_append_left _ row,decode⟩

theorem a_redundant_read_preserves_unfiltered_K2416 (s : GeneralDeclarativeHead320.State) (root site : Nat) :
    AliasCycle (withRedundantRead s root) (observed (withRedundantRead s root)) site ↔
    AliasCycle s (observed s) site := by
  have aliases : GeneralDeclarativeLowerKnown321.Alias (withRedundantRead s root) = GeneralDeclarativeLowerKnown321.Alias s := by
    funext x y
    exact propext (a_redundant_read_preserves_actual_raw_alias416 s root x y)
  have original : observed (withRedundantRead s root) = observed s := by
    funext x shape
    exact propext (a_redundant_read_preserves_raw_observation416 s root x shape)
  unfold AliasCycle GeneralDeclarativeK2Graph321.aliasView
  rw [aliases,original]

theorem a_redundant_read_preserves_raw_guard416 (s : GeneralDeclarativeHead320.State) (root site : Nat)
    (w : List410.ExactEscapeWire) :
    List410.checkExactEscape (withRedundantRead s root) site w =
      List410.checkExactEscape s site w := by
  simp [List410.checkExactEscape,List410.aliasRanks,List410.aliasRow,List410.exactShapeEscape,
    withRedundantRead,idempotentRow,
    GeneralDeclarativeGraphRows321.shapeOf]

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
