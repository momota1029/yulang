import Yulang.GeneralSourceRoleCstWireBinding294

/-! Reusing a brand or retaining the compact parse cannot bind a receipt if
an original token kind changed. -/
namespace Yulang.GeneralSourceRoleCstBindingControl294
open GeneralSourceRoleCstWire293 (Wire decode decodeList)
open GeneralSourceRoleCstWireBinding294 (same same_exact)

theorem final_newline_compacts_same (pre : List Wire) :
    decodeList (pre ++ [.token "Newline" "\n"]) =
      decodeList (pre ++ [.token "Whitespace" "\n"]) := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    change (decode x).bind (fun t => (decodeList (xs ++ _)).map (t::·)) = _
    rw [ih]
    rfl

theorem root_tail_kind_collision (pre : List Wire) :
    decode (.node "Root" (pre ++ [.token "Newline" "\n"])) =
      decode (.node "Root" (pre ++ [.token "Whitespace" "\n"])) ∧
    same (.node "Root" (pre ++ [.token "Newline" "\n"]))
      (.node "Root" (pre ++ [.token "Whitespace" "\n"])) = false := by
  constructor
  · simp [decode,final_newline_compacts_same pre]
  · cases h : same (.node "Root" (pre ++ [.token "Newline" "\n"]))
      (.node "Root" (pre ++ [.token "Whitespace" "\n"])) with
    | false => rfl
    | true =>
      have names := (Wire.node.inj ((same_exact ..).mp h)).2
      have tail := List.append_cancel_left names
      have k := (Wire.token.inj (List.cons.inj tail).1).1
      exact False.elim ((by decide : "Newline" ≠ "Whitespace") k)

end Yulang.GeneralSourceRoleCstBindingControl294
