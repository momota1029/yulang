import Yulang.GeneralSourceRoleCstRunExtent294

/-! Controls for original label, ownership, and touching byte constraints. -/
namespace Yulang.GeneralSourceRoleCstRunControls294
open GeneralSourceRoleCstOriginalMarks294 (Origin Element)
open GeneralSourceRoleCstErrorRuns294 (bridge runs)
open GeneralSourceRoleCstRunExtent294 (extent)
open GeneralSourceRoleCstTree293 (Path)

def tokenAt (p : Path) (lo hi : Nat) (tag : String := "Error") : Origin :=
  ⟨⟨p,.error,⟨lo,hi⟩⟩,tag,.token⟩

def a : Origin := tokenAt [1] 49 50
def b : Origin := tokenAt [2] 50 51
def c : Origin := tokenAt [3] 51 58

theorem recorded_range_model :
    runs [a,b,c] = [[a,b,c]] ∧ extent [a,b,c] = some ⟨49,58⟩ := ⟨rfl,rfl⟩

theorem no_crossing_different_owner :
    bridge (tokenAt [0,1] 0 1) (tokenAt [2,2] 1 2) = false := rfl

theorem ordinal_gap_even_if_spans_touch :
    bridge (tokenAt [1] 0 1) (tokenAt [3] 1 2) = false := rfl

theorem byte_gap_even_if_ordinals_touch :
    bridge (tokenAt [1] 0 1) (tokenAt [2] 2 3) = false := rfl

theorem normalized_error_is_not_original_error_token :
    bridge a (tokenAt [2] 50 51 "Unknown") = false ∧
    bridge a {b with originalMode := .node} = false := ⟨rfl,rfl⟩

#guard bridge a b
#guard !(bridge a (tokenAt [2] 50 51 "Unknown"))

end Yulang.GeneralSourceRoleCstRunControls294
