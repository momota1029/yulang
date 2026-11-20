import Yulang.GeneralSourceRoleCstGroupAnchor294

/-! Even two distinct portable runs can share an empty byte range. The
strict matcher does not use a byte range as occurrence identity. -/
set_option maxRecDepth 10000
namespace Yulang.GeneralSourceRoleCstGroupFixture294
open GeneralSourceRoleCstWire293 (Wire decode)
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstGroupAnchor294 (unique candidates outside)

def twoRuns : Wire := .node "Root"
  [.node "BindingHeader" [.token "Error" ""],.node "BindingBody" [.token "Error" ""]]

def twoTrees : Tree := .node .root
  [.node .other [.token .error ""],.node .other [.token .error ""]]

theorem ambiguous_has_two_runs :
    decode twoRuns = some twoTrees ∧ (candidates twoRuns twoTrees ⟨0,0⟩).length = 2 :=
  ⟨rfl,rfl⟩

theorem ambiguous_extent_refused : unique twoRuns twoTrees ⟨0,0⟩ = none := rfl

theorem unavailable_range_refused : unique twoRuns twoTrees ⟨0,1⟩ = none := rfl

#guard (unique twoRuns twoTrees ⟨0,0⟩).isNone

end Yulang.GeneralSourceRoleCstGroupFixture294
