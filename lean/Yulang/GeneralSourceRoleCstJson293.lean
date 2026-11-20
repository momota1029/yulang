import Lean.Data.Json.Basic
import Yulang.GeneralSourceRoleCstWirePaths293

/-! Bounded input transport over JSON values. The exact property concerns
the explicitly tagged array schema and does not parse Yulang source. -/
namespace Yulang.GeneralSourceRoleCstJson293
open Lean (Json)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleExport292 (collect collect_exact Aligned)

mutual
def encode : Wire → Json
  | .token tag text => .arr #[.str "token",.str tag,.str text]
  | .node tag cs => .arr #[.str "node",.str tag,.arr (encodeList cs).toArray]
def encodeList : List Wire → List Json
  | [] => []
  | w::ws => encode w :: encodeList ws
end

mutual
def depth : Wire → Nat
  | .token _ _ => 1
  | .node _ cs => depthList cs + 1
def depthList : List Wire → Nat
  | [] => 0
  | w::ws => max (depth w) (depthList ws)
end

def read : Nat → Json → Option Wire
  | 0,_ => none
  | fuel+1,.arr items =>
    match items.toList with
    | [.str "token",.str tag,.str text] => some (.token tag text)
    | [.str "node",.str tag,.arr children] =>
      (collect (read fuel) children.toList).map (Wire.node tag)
    | _ => none
  | _+1,_ => none

theorem depth_positive (w : Wire) : 0 < depth w := by cases w <;> simp [depth]

theorem list_prop (fuel : Nat) (xs : List Json) (ws : List Wire) :
    Aligned (fun j w => encode w = j ∧ depth w ≤ fuel) xs ws ↔
      encodeList ws = xs ∧ depthList ws ≤ fuel := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨rfl,Nat.zero_le _⟩
    | cons front _ ih =>
      exact ⟨by simp only [encodeList,front.1,ih.1],
        by simp only [depthList,Nat.max_le]; exact ⟨front.2,ih.2⟩⟩
  · rintro ⟨rfl,bound⟩
    induction ws with
    | nil => exact .nil
    | cons a as ih =>
      have sizes := Nat.max_le.mp bound
      exact .cons ⟨rfl,sizes.1⟩ (ih sizes.2)

theorem read_exact (fuel : Nat) (j : Json) (w : Wire) :
    read fuel j = some w ↔ encode w = j ∧ depth w ≤ fuel := by
  induction fuel generalizing j w with
  | zero =>
    constructor
    · intro h; cases h
    · intro h; have z := depth_positive w; omega
  | succ fuel ih =>
    have listExact : ∀ (xs : List Json) (ws : List Wire),
        collect (read fuel) xs = some ws ↔ encodeList ws = xs ∧ depthList ws ≤ fuel :=
      fun xs ws => (collect_exact _ _ ih xs ws).trans (list_prop fuel xs ws)
    constructor
    · intro h
      cases j <;> try cases h
      rename_i arr
      change (match arr.toList with
        | [.str "token",.str tag,.str text] => some (.token tag text)
        | [.str "node",.str tag,.arr children] =>
          (collect (read fuel) children.toList).map (Wire.node tag)
        | _ => none) = some w at h
      generalize shape : arr.toList = xs at h
      split at h
      · rename_i _ tag text
        cases Option.some.inj h
        exact ⟨by apply congrArg Json.arr; exact Array.toList_inj.mp shape.symm,
          Nat.succ_le_succ (Nat.zero_le _)⟩
      · rename_i _ tag children
        cases ready : collect (read fuel) children.toList with
        | none => simp [ready] at h
        | some ws =>
          have same : Wire.node tag ws = w := by simpa [ready] using h
          subst w
          obtain ⟨enc,deep⟩ := (listExact _ _).mp ready
          exact ⟨by apply congrArg Json.arr; rw [enc,Array.toArray_toList]; exact Array.toList_inj.mp shape.symm,
            Nat.succ_le_succ deep⟩
      · cases h
    · rintro ⟨rfl,bound⟩
      cases w with
      | token => rfl
      | node tag ws =>
        have exactChildren : collect (read fuel) (encodeList ws) = some ws :=
          (listExact ..).mpr ⟨rfl,Nat.le_of_succ_le_succ bound⟩
        simp [read,encode,exactChildren]

end Yulang.GeneralSourceRoleCstJson293
