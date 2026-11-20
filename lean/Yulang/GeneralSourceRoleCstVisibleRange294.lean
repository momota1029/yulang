import Yulang.GeneralSourceRoleCstRunVisibility294

/-! Demand source-visible plain token ownership in addition to the exact
range and scope check. Opaque recovery must not be mistaken for a token run. -/
namespace Yulang.GeneralSourceRoleCstVisibleRange294
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstWire293 (Wire Transfer decode decode_exact)
open GeneralSourceRoleCstOriginalMarks294 (Origin)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstRunVisibility294 (visible Visible visible_exact)
open GeneralSourceRoleCstGroupAnchor294 (unique outside outside_exact)

def checkVisible (wire : Wire) (range : Extent) (p : Path) : Bool :=
  match wire with
  | .node "Root" _ =>
    match decode wire with
    | none => false
    | some root =>
      match unique wire root range with
      | none => false
      | some row => outside p row && row.all (fun o => visible o.occurrence.path wire)
  | _ => false

theorem visible_range_exact (wire : Wire) (r : Extent) (p : Path) :
    checkVisible wire r p = true ↔
      ∃ children root row, wire = .node "Root" children ∧ Transfer wire root ∧
        unique wire root r = some row ∧
        (∀ item ∈ row, (¬ p <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: p) ∧
          Visible item.occurrence.path wire) := by
  have reduce (children : List Wire) :
      checkVisible (.node "Root" children) r p = true ↔
        ∃ root row, Transfer (.node "Root" children) root ∧
          unique (.node "Root" children) root r = some row ∧
          (∀ item ∈ row, (¬ p <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: p) ∧
            Visible item.occurrence.path (.node "Root" children)) := by
    cases h : decode (.node "Root" children) with
    | none => simp [checkVisible, ← decode_exact,h]
    | some root =>
      cases k : unique (.node "Root" children) root r with
      | none => simp [checkVisible, ← decode_exact,h,k]
      | some row => simp [checkVisible, ← decode_exact,h,k,outside_exact,List.all_eq_true,
          visible_exact,forall_and]
  cases wire with
  | token label src => simp [checkVisible]
  | node label cs =>
    by_cases h : label = "Root"
    · subst label; simpa using reduce cs
    · have reject : checkVisible (.node label cs) r p = false := by
        unfold checkVisible
        split
        · rename_i d same
          have wrong := (Wire.node.inj same).1
          exact False.elim (h wrong)
        · rfl
      simp [reject,h]

def depthWrapped : Wire := .node "Root" [.node "NestingTooDeep" [.token "Error" "雪"]]
def suppresses : Wire := .node "Root" [.node "Error" [.token "Error" "雪"]]
def emptyToken : Wire := .node "Root" [.token "Error" ""]

theorem opacity_is_not_token_run : GeneralSourceRoleCstRangeReceipt294.check depthWrapped ⟨0,3⟩ [1] = true ∧
    checkVisible depthWrapped ⟨0,3⟩ [1] = false := ⟨rfl,rfl⟩

theorem error_node_suppresses_direct_tokens :
    GeneralSourceRoleCstRangeReceipt294.check suppresses ⟨0,3⟩ [1] = true ∧
    checkVisible suppresses ⟨0,3⟩ [1] = false := ⟨rfl,rfl⟩

theorem empty_token_is_not_a_rust_run :
    GeneralSourceRoleCstRangeReceipt294.check emptyToken ⟨0,0⟩ [1] = true ∧
    checkVisible emptyToken ⟨0,0⟩ [1] = false := ⟨rfl,rfl⟩

end Yulang.GeneralSourceRoleCstVisibleRange294
