import Yulang.GeneralDeclarativeWitnessMixedPathLedger356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAddressLinear356
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeWitnessPathOrder352 (preorder branchOrder)
open GeneralDeclarativeWitnessMixedLedger356 (Entry)

theorem branch_address_ne (pre : List Nat) {i j : Nat} {xs ys : List Nat} (later : i < j) :
    pre ++ (i :: xs) ≠ pre ++ (j :: ys) := by
  intro equal
  have heads := List.cons.inj ((List.append_right_inj pre).mp equal)
  exact (Nat.ne_of_lt later) heads.1

mutual
theorem tree_addresses (pre : List Nat) (t : Tree) :
    (preorder pre t).Nodup ∧ ∀ path ∈ preorder pre t,∃ tail,path = pre ++ tail := by
  cases t with
  | pending => simp [preorder.eq_def]
  | ambiguous => simp [preorder.eq_def]
  | rejected => simp [preorder.eq_def]
  | selected key kids =>
    rw [preorder.eq_def]
    change (pre :: branchOrder pre 0 kids).Nodup ∧
      ∀ path ∈ pre :: branchOrder pre 0 kids,∃ tail,path = pre ++ tail
    have branches := descendants pre 0 kids
    refine ⟨List.nodup_cons.mpr ⟨?_,branches.1⟩,?_⟩
    · intro repeated
      obtain ⟨i,tail,_,bad⟩ := branches.2 pre repeated
      have badLen := congrArg List.length bad
      simp only [List.length_append,List.length_cons] at badLen
      omega
    · intro path hit
      rcases List.mem_cons.mp hit with rfl|under
      · exact ⟨[],(List.append_nil _).symm⟩
      · obtain ⟨i,tail,_,whereAt⟩ := branches.2 path under
        exact ⟨i::tail,whereAt⟩
termination_by sizeOf t

theorem descendants (pre : List Nat) (base : Nat) (kids : List Tree) :
    (branchOrder pre base kids).Nodup ∧
      ∀ path ∈ branchOrder pre base kids,∃ i tail,base ≤ i ∧ path = pre ++ (i :: tail) := by
  cases kids with
  | nil => simp [branchOrder.eq_def]
  | cons top rest =>
    rw [branchOrder.eq_def]
    change (preorder (pre ++ [base]) top ++ branchOrder pre (base+1) rest).Nodup ∧
      ∀ path ∈ preorder (pre ++ [base]) top ++ branchOrder pre (base+1) rest,
        ∃ i tail,base ≤ i ∧ path = pre ++ (i :: tail)
    have first := tree_addresses (pre ++ [base]) top
    have continuing := descendants pre (base+1) rest
    refine ⟨List.nodup_append.mpr ⟨first.1,continuing.1,?_⟩,?_⟩
    · intro a inFirst b inRest
      obtain ⟨start,atFirst⟩ := first.2 a inFirst
      obtain ⟨j,last,greater,atRest⟩ := continuing.2 b inRest
      rw [atFirst,List.append_assoc,atRest]
      exact branch_address_ne pre greater
    · intro path there
      rcases List.mem_append.mp there with here|other
      · obtain ⟨tail,exactly⟩ := first.2 path here
        exact ⟨base,tail,Nat.le_refl _,exactly.trans (List.append_assoc ..)⟩
      · obtain ⟨i,tail,greater,exactly⟩ := continuing.2 path other
        exact ⟨i,tail,by omega,exactly⟩
termination_by sizeOf kids
end

theorem unique_report_addresses {p s w} (checked : GeneralDeclarativeWitnessRecursiveSource356.Found p s w) :
    (w.report.outputs.map Entry.path).Nodup := by
  rw [GeneralDeclarativeWitnessMixedPathLedger356.report_paths checked]
  exact (tree_addresses ..).1

theorem entries_address_injective (rows : List Entry) (linear : (rows.map Entry.path).Nodup)
    {a b : Entry} (ha : a ∈ rows) (hb : b ∈ rows)
    (same : a.path = b.path) : a = b := by
  induction rows with
  | nil => cases ha
  | cons first rest ih =>
    change (first.path :: rest.map Entry.path).Nodup at linear
    have none := (List.nodup_cons.mp linear).1
    have tail := (List.nodup_cons.mp linear).2
    rcases List.mem_cons.mp ha with rfl|inTail <;> rcases List.mem_cons.mp hb with rfl|inTail'
    · rfl
    · exact False.elim (none (same.symm ▸ List.mem_map_of_mem (f := Entry.path) inTail'))
    · exact False.elim (none (same ▸ List.mem_map_of_mem (f := Entry.path) inTail))
    · exact ih tail inTail inTail'

theorem one_write_entry_per_compiler_path {p s w}
    (checked : GeneralDeclarativeWitnessRecursiveSource356.Found p s w)
    {a b : Entry} (ha : a ∈ w.report.outputs) (hb : b ∈ w.report.outputs)
    (same : a.path = b.path) : a = b :=
  entries_address_injective _ (unique_report_addresses checked) ha hb same

end Yulang.GeneralDeclarativeWitnessAddressLinear356
