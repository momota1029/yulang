import Yulang.CommonRoleMergedCaptureBoundary

/-! The canonical record-tail component of stable descent. This works for
arbitrary payload carriers and weights, using the actual computed residual.
There is no arbitrary masked tail substitution and no full-resolver claim. -/
namespace Yulang.CommonRoleStableRecordResidual

open CommonRoleCanonicalRows (Row normalize lookup capture residual mass)

def check (labels : List Nat) : Bool := !labels.isEmpty

def headMatches (labels : List Nat) (goal : Row Payload) : Bool :=
  labels.all (fun label => (lookup label (normalize goal)).isSome)

theorem lookup_member (label : Nat) (row : Row Payload) (payload : Payload)
    (found : lookup label row = some payload) : (label, payload) ∈ row := by
  induction row with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : label = key
      · subst key
        have equal : value = payload := by simpa [lookup] using found
        subst value
        exact List.mem_cons_self ..
      · have tail : lookup label rest = some payload := by simpa [lookup, same] using found
        exact List.mem_cons_of_mem _ (ih tail)

theorem matching_explicit_entry (labels : List Nat) (goal : Row Payload)
    (accepted : check labels = true) (matched : headMatches labels goal = true) :
    ∃ entry ∈ normalize goal, entry.1 ∈ labels := by
  cases labels with
  | nil => cases accepted
  | cons label rest =>
      have present := List.all_eq_true.mp matched label (List.mem_cons_self ..)
      obtain ⟨payload, found⟩ := Option.isSome_iff_exists.mp present
      exact ⟨(label, payload), lookup_member label (normalize goal) payload found, List.mem_cons_self ..⟩

def size (weight : Payload → Nat) (row : Row Payload) : Nat := 1 + mass weight (normalize row)

theorem capture_is_normal (labels : List Nat) (goal : Row Payload) :
    normalize (capture labels goal) = capture labels goal := by
  apply CommonRoleCanonicalRows.normalize_of_unique
  exact (CommonRoleCanonicalRows.normalize_unique goal).sublist
    ((List.filter_sublist ..).map Prod.fst)

def count (weight : Payload → Nat) : Row Payload → Nat
  | [] => 0
  | (_, payload) :: rest => weight payload + count weight rest

theorem residual_count_le (weight : Payload → Nat) (labels : List Nat) (row : Row Payload) :
    count weight (residual labels row) ≤ count weight row := by
  induction row with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      by_cases removed : entry.1 ∈ labels <;> simp_all [residual, count] <;> omega

theorem checked_residual_decreases (labels : List Nat) (goal : Row Payload)
    (accepted : check labels = true) (matched : headMatches labels goal = true)
    (weight : Payload → Nat) (occurrences : Nat → Payload → Nat) :
    size weight (capture labels goal) < size weight goal ∧
      ∀ name, count (occurrences name) (normalize (capture labels goal)) ≤
        count (occurrences name) (normalize goal) := by
  obtain ⟨entry, present, removed⟩ := matching_explicit_entry labels goal accepted matched
  constructor
  · have strict := CommonRoleCanonicalRows.residual_mass_lt weight labels (normalize goal) entry present removed
    change 1 + mass weight (normalize (capture labels goal)) < 1 + mass weight (normalize goal)
    rw [capture_is_normal]
    exact Nat.add_lt_add_left strict 1
  · intro name
    rw [capture_is_normal]
    exact residual_count_le (occurrences name) labels (normalize goal)

theorem repeated_label_allowed (label : Nat) : check [label, label] = true := rfl
theorem empty_head_rejected : check [] = false := rfl

end Yulang.CommonRoleStableRecordResidual
