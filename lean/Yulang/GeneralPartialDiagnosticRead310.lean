import Yulang.GeneralGeneratedDictionaryScope299

/-! Check a returned finite diagnostic tree against supplied certified frontier
rows. A selected parent retains pending, rejected or ambiguous children.
This is not a solver and does not prove that saturation returns. -/
namespace Yulang.GeneralPartialDiagnosticRead310
open CommonRoleOutermostResolver (Frontier Tree Resolves All₂)
open GeneralGeneratedDictionaryScope299 (map_all)

abbrev Read := Nat → Option (Frontier Nat)

def mapFrontier (decode : Nat → α) : Frontier Nat → Frontier α
  | .pending => .pending
  | .rejected => .rejected
  | .ambiguous => .ambiguous
  | .selected key kids => .selected key (kids.map decode)

def check (read : Read) : Nat → Nat → Tree → Bool
  | 0,_,_ => false
  | n+1,i,t =>
    match read i,t with
    | some .pending,.pending => true
    | some .rejected,.rejected => true
    | some .ambiguous,.ambiguous => true
    | some (.selected key kids),.selected called actual =>
      key == called && rows (check read n) kids actual
    | _,_ => false
where
  rows (visit : Nat → Tree → Bool) : List Nat → List Tree → Bool
    | [],[] => true
    | i::is,t::ts => visit i t && rows visit is ts
    | _,_ => false

theorem rows_exact (visit : Nat → Tree → Bool) (is : List Nat) (ts : List Tree) :
    check.rows visit is ts = true ↔ All₂ (fun i t => visit i t = true) is ts := by
  induction is generalizing ts with
  | nil =>
    cases ts with
    | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
    | cons t ts => constructor <;> intro h <;> cases h
  | cons i is ih =>
    cases ts with
    | nil => constructor <;> intro h <;> cases h
    | cons t ts =>
      simp only [check.rows,Bool.and_eq_true,ih]
      exact ⟨fun h => .cons h.1 h.2,fun h => by cases h with | cons a b => exact ⟨a,b⟩⟩

def Faithful (read : Read) (decode : Nat → α) (localRule : α → Frontier α → Prop) : Prop :=
  ∀ i r, read i = some r → localRule (decode i) (mapFrontier decode r)

theorem sound (read : Read) (decode : Nat → α) (localRule : α → Frontier α → Prop)
    (faithful : Faithful read decode localRule) (fuel i : Nat) (tree : Tree)
    (accepted : check read fuel i tree = true) :
    Resolves localRule (decode i) tree := by
  induction fuel generalizing i tree with
  | zero => cases accepted
  | succ n ih =>
    cases rowEq : read i with
    | none => cases tree <;> simp [check,rowEq] at accepted
    | some row =>
      have actual := faithful i row rowEq
      cases row <;> cases tree <;> simp only [check,rowEq,Bool.and_eq_true,beq_iff_eq] at accepted
      all_goals try contradiction
      · exact .pending actual
      · obtain ⟨rfl,ordered⟩ := accepted
        exact .selected actual (map_all decode ih ((rows_exact ..).mp ordered))
      · exact .ambiguous actual
      · exact .rejected actual

/-- The readback can be partial. A checked return needs only sound decoded rows
    and the actual reached halted endpoint, never a guarantee of reaching it. -/
theorem returned {v : B4Target.Vocabulary} (b : B4TargetV8.SourceBoundary v) (r : v.Registry)
    (start after : v.State) (d : v.Demand) (walk : B4Target.Steps (b.Step r d) start after)
    (initial : b.Initial r d start) (halted : ∀ next, ¬ b.Step r d after next)
    (read : Read) (decode : Nat → v.Demand)
    (faith : Faithful read decode (B4TargetV8.Local b r after))
    (fuel i : Nat) (tree : Tree) (root : decode i = d)
    (accepted : check read fuel i tree = true) :
    B4TargetV8.Reachable b r d after ∧
    (∀ next, ¬ b.Step r d after next) ∧ Resolves (B4TargetV8.Local b r after) d tree :=
  ⟨⟨start,initial,walk⟩,halted,root ▸ sound read decode _ faith fuel i tree accepted⟩

end Yulang.GeneralPartialDiagnosticRead310
