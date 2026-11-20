import Yulang.GeneralSourceRoleCstTypeRules293
import Yulang.GeneralSourceRoleCstPath293

/-! Exact traversal for the adapter's marked recovery kinds. A genuine
Rust serializer must classify all its recovery kinds into these marks. -/
namespace Yulang.GeneralSourceRoleCstRecovery293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293
open GeneralSourceRoleCstPath293 (follow)

abbrev Plain (k : Kind) : Prop := k ≠ .missing ∧ k ≠ .invalid ∧ k ≠ .error

def TreePlain (root : Tree) : Prop :=
  ∀ p t, follow p root = some t → Plain t.kind

def ListPlain (xs : List Tree) : Prop :=
  ∀ (i : Nat) t, xs[i]? = some t → TreePlain t

mutual
theorem clean_tree_exact (root : Tree) : cleanTree root = true ↔ TreePlain root := by
  cases root with
  | token k s =>
    change decide (Plain k) = true ↔ TreePlain (.token k s)
    rw [decide_eq_true_eq]
    constructor
    · intro safe p t h
      cases p with
      | nil => cases Option.some.inj h; exact safe
      | cons x xs => cases h
    · intro all
      exact all [] _ rfl
  | node k children =>
    change (decide (Plain k) && cleanList children) = true ↔ TreePlain (.node k children)
    rw [Bool.and_eq_true,decide_eq_true_eq,clean_list_exact]
    constructor
    · rintro ⟨safe,below⟩ p t read
      cases p with
      | nil => cases Option.some.inj read; exact safe
      | cons i tail =>
        cases place : children[i]? with
        | none => simp [follow,place] at read
        | some child =>
          have h : follow tail child = some t := by simpa [follow,place] using read
          exact below i child place tail t h
    · intro all
      refine ⟨all [] _ rfl,?_⟩
      intro i t place p child found
      apply all (i :: p) child
      simp [follow,place,found]
theorem clean_list_exact (xs : List Tree) : cleanList xs = true ↔ ListPlain xs := by
  cases xs with
  | nil => exact ⟨(by intro _ i t bad; cases bad),fun _ => rfl⟩
  | cons x xs =>
    rw [cleanList,Bool.and_eq_true,clean_tree_exact,clean_list_exact]
    constructor
    · rintro ⟨one,others⟩ i t read
      cases i with
      | zero => cases Option.some.inj read; exact one
      | succ j => exact others j t read
    · intro all
      exact ⟨all 0 x rfl,fun j t read => all (j+1) t read⟩
end

theorem recovery_descendant_blocks_binding (cs : List Tree) (i : Nat) (node : Tree)
    (p : Path) (marked : Tree) (direct : cs[i]? = some node)
    (deep : follow p node = some marked) (bad : ¬ Plain marked.kind) :
    GeneralSourceRoleCstBody293.classify (.node .binding cs) = none := by
  have notClean : cleanList cs ≠ true := fun h => bad ((clean_list_exact cs).mp h i node direct p marked deep)
  simp [GeneralSourceRoleCstBody293.classify,notClean]

end Yulang.GeneralSourceRoleCstRecovery293
