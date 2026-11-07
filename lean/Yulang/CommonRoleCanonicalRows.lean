import Yulang.CommonRoleFiniteTailExamples
import Yulang.VariantsMerged

/-!
# Canonical role-head record subtraction

An independent capture is the concrete row minus the explicit visible labels,
not an arbitrary Common assignment satisfying a masked equation. Unknown goal
tails do not enter this determined-row operation. The weighted partition is
the record component of the intended global descent proof.
-/

namespace Yulang.CommonRoleCanonicalRows

abbrev Row (Payload : Type) := List (Nat × Payload)

def residual (labels : List Nat) (row : Row Payload) : Row Payload :=
  row.filter (fun entry => !labels.contains entry.1)

def selected (labels : List Nat) (row : Row Payload) : Row Payload :=
  row.filter (fun entry => labels.contains entry.1)

/-- First-field-wins. Payload normalization is a separate structural walk. -/
def normalize : Row Payload → Row Payload
  | [] => []
  | (label, payload) :: rest =>
      (label, payload) :: residual [label] (normalize rest)

def lookup (label : Nat) : Row Payload → Option Payload
  | [] => none
  | (key, payload) :: rest => if label = key then some payload else lookup label rest

@[simp] theorem mem_residual (labels : List Nat) (row : Row Payload) (entry : Nat × Payload) :
    entry ∈ residual labels row ↔ entry ∈ row ∧ entry.1 ∉ labels := by
  simp [residual]

@[simp] theorem mem_selected (labels : List Nat) (row : Row Payload) (entry : Nat × Payload) :
    entry ∈ selected labels row ↔ entry ∈ row ∧ entry.1 ∈ labels := by
  simp [selected]

theorem residual_excludes (labels : List Nat) (row : Row Payload) (entry : Nat × Payload)
    (member : entry ∈ residual labels row) : entry.1 ∉ labels := (mem_residual _ _ _).mp member |>.2

theorem residual_commute (first last : List Nat) (row : Row Payload) :
    residual first (residual last row) = residual last (residual first row) := by
  simp only [residual, List.filter_filter]
  congr 1
  funext entry
  exact Bool.and_comm ..

theorem residual_idempotent (labels : List Nat) (row : Row Payload) :
    residual labels (residual labels row) = residual labels row := by
  simp [residual, List.filter_filter]

theorem residual_map (labels : List Nat) (mapPayload : Payload → Other) (row : Row Payload) :
    residual labels (row.map (fun entry => (entry.1, mapPayload entry.2))) =
      (residual labels row).map (fun entry => (entry.1, mapPayload entry.2)) := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      by_cases removed : entry.1 ∈ labels <;> simp_all [residual]

theorem lookup_residual (labels : List Nat) (row : Row Payload) (label : Nat) :
    lookup label (residual labels row) = if label ∈ labels then none else lookup label row := by
  induction row with
  | nil => simp [lookup, residual]
  | cons entry rest ih =>
      rcases entry with ⟨key, payload⟩
      by_cases same : label = key
      · subst key
        by_cases removed : label ∈ labels <;> simp_all [lookup, residual]
      · by_cases removedKey : key ∈ labels <;>
          by_cases removedLabel : label ∈ labels <;> simp_all [lookup, residual]

theorem lookup_normalize (row : Row Payload) (label : Nat) : lookup label (normalize row) = lookup label row := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, payload⟩
      by_cases same : label = key <;> simp [normalize, lookup, same, lookup_residual, ih]

theorem normalize_unique (row : Row Payload) : ((normalize row).map Prod.fst).Nodup := by
  induction row with
  | nil => simp [normalize]
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [normalize, List.map_cons, List.nodup_cons]
      constructor
      · intro present
        obtain ⟨other, member, same⟩ := List.mem_map.mp present
        exact residual_excludes [label] _ other member (by simp [same])
      · exact ih.sublist ((List.filter_sublist ..).map Prod.fst)

theorem normalize_of_unique (row : Row Payload) (unique : (row.map Prod.fst).Nodup) : normalize row = row := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨label, payload⟩
      simp only [List.map_cons, List.nodup_cons] at unique
      rw [normalize, ih unique.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro other member
      have different : other.1 ≠ label := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨other, member, same⟩)
      simp [different]

theorem normalize_idempotent (row : Row Payload) : normalize (normalize row) = normalize row :=
  normalize_of_unique _ (normalize_unique row)

def capture (labels : List Nat) (row : Row Payload) : Row Payload := residual labels (normalize row)

def Captures (labels : List Nat) (row tail : Row Payload) : Prop := tail = capture labels row

theorem capture_unique (labels : List Nat) (row first last : Row Payload)
    (a : Captures labels row first) (b : Captures labels row last) : first = last := a.trans b.symm

theorem capture_no_hidden (labels : List Nat) (row : Row Payload) (entry : Nat × Payload)
    (member : entry ∈ capture labels row) : entry.1 ∉ labels := residual_excludes _ _ _ member

theorem capture_normalize (labels : List Nat) (row : Row Payload) :
    capture labels (normalize row) = capture labels row := by simp [capture, normalize_idempotent]

theorem former_clock_removed (payload : Payload) : capture [0] [(0, payload)] = [] := by
  simp [capture, normalize, residual]

def mass (weight : Payload → Nat) : Row Payload → Nat
  | [] => 0
  | (_, payload) :: rest => 1 + weight payload + mass weight rest

theorem mass_partition (weight : Payload → Nat) (labels : List Nat) (row : Row Payload) :
    mass weight (selected labels row) + mass weight (residual labels row) = mass weight row := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      by_cases removed : entry.1 ∈ labels <;> simp_all [selected, residual, mass] <;> omega

theorem residual_mass_le (weight : Payload → Nat) (labels : List Nat) (row : Row Payload) :
    mass weight (residual labels row) ≤ mass weight row := by
  have partition := mass_partition weight labels row
  omega

theorem selected_positive (weight : Payload → Nat) (labels : List Nat) (row : Row Payload)
    (entry : Nat × Payload) (present : entry ∈ row) (removed : entry.1 ∈ labels) :
    0 < mass weight (selected labels row) := by
  induction row with
  | nil => contradiction
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | present
      · simp [selected, removed, mass]; omega
      · have positive := ih present
        by_cases headRemoved : first.1 ∈ labels <;> simp_all [selected, mass] <;> omega

theorem residual_mass_lt (weight : Payload → Nat) (labels : List Nat) (row : Row Payload)
    (entry : Nat × Payload) (present : entry ∈ row) (removed : entry.1 ∈ labels) :
    mass weight (residual labels row) < mass weight row := by
  have partition := mass_partition weight labels row
  have positive := selected_positive weight labels row entry present removed
  omega

end Yulang.CommonRoleCanonicalRows
