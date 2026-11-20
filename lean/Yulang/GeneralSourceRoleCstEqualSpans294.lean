import Yulang.GeneralSourceRoleCstPathFidelity294

/-! Equal ranges do not identify a CST node. Two independent zero-width
marks after a multibyte token must retain their distinct raw addresses. -/
namespace Yulang.GeneralSourceRoleCstEqualSpans294
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstWire293 (Wire decode)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstOriginalMarks294 (Origin original Element)
open GeneralSourceRoleCstGroupAnchor294 (unique)
open GeneralSourceRoleCstRangeReceipt294 (check)

def equalWidthWire : Wire := .node "Root"
  [.token "Identifier" "雪",.node "Missing" [],.token "Unknown" "",.token "Error" "終"]

def equalWidthTree : Tree := .node .root
  [.token .identifier "雪",.node .missing [],.token .error "",.token .error "終"]

theorem equal_width_decode : decode equalWidthWire = some equalWidthTree := rfl

theorem equal_width_marks_both_retained :
    (original equalWidthWire equalWidthTree).map (fun o => o.occurrence.path) =
      [[1],[2],[3]] ∧
    (original equalWidthWire equalWidthTree).map (fun o => o.occurrence.extent) =
      [⟨3,3⟩,⟨3,3⟩,⟨3,6⟩] ∧
    (original equalWidthWire equalWidthTree).map (fun o => (o.originalTag,o.originalMode)) =
      [("Missing",.node),("Unknown",.token),("Error",.token)] := ⟨rfl,rfl,rfl⟩

theorem zero_width_non_error_not_anchored :
    unique equalWidthWire equalWidthTree ⟨3,3⟩ = none ∧
    check equalWidthWire ⟨3,6⟩ [0] = true ∧
    check equalWidthWire ⟨3,6⟩ [3] = false := ⟨rfl,rfl,rfl⟩

end Yulang.GeneralSourceRoleCstEqualSpans294
