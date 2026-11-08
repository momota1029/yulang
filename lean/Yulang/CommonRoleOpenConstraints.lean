import Yulang.CommonRoleSettledConstraints

/-! Genuine two-slot capture constraints. No endpoint equality or chosen
center is used. This module identifies exactly the state change which the
settled no-op recollection theorem cannot erase. -/
namespace Yulang.CommonRoleOpenConstraints
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSettledConstraints (State)

/-- Lower and upper are distinct fresh slots; all old slots shift twice. -/
def slots (names : List Nat) : CommonRoleCandidateConstraints.Bindings (n + 2) :=
  names.map (fun name => (name, (0, 1)))

def extend (lower upper : Comp Common.model) (assignment : Fin n → Comp Common.model) :
    Fin (n + 2) → Comp Common.model := Fin.cases lower (Fin.cases upper assignment)

def shift (i : Fin n) : Fin (n + 2) := i.succ.succ

theorem bounds_slots (names : List Nat) (name : Nat) (pair : Fin (n + 2) × Fin (n + 2))
    (h : pair ∈ CommonRoleCandidateConstraints.bounds (slots names) name) : pair = (0, 1) := by
  obtain ⟨⟨key, pair'⟩, member, found⟩ := List.mem_filterMap.mp h
  obtain ⟨original, _, equal⟩ := List.mem_map.mp member
  cases equal
  split at found <;> simp_all

theorem bounds_present (names : List Nat) (name : Nat) (member : name ∈ names) :
    (0, 1) ∈ CommonRoleCandidateConstraints.bounds (slots (n := n) names) name := by
  apply List.mem_filterMap.mpr
  refine ⟨(name, (0, 1)), List.mem_map.mpr ⟨name, member, rfl⟩, ?_⟩
  simp

theorem compatible_exact (names : List Nat) (assignment : Fin (n + 2) → Comp Common.model) :
    CommonRoleCandidateConstraints.Compatible (slots names) assignment ↔
      names = [] ∨ Common.Subtype (assignment 0).1 (assignment 1).1 := by
  constructor
  · intro h
    cases names with
    | nil => exact Or.inl rfl
    | cons name rest =>
      right
      exact h name (by simp [slots, CommonRoleCandidateConstraints.names]) (0, 1) (bounds_present _ _ (by simp))
        (0, 1) (bounds_present _ _ (by simp))
  · rintro (empty | compatible)
    · subst names
      intro name member
      simp [slots, CommonRoleCandidateConstraints.names] at member
    · intro name _ first present last included
      rw [bounds_slots names name first present, bounds_slots names name last included]
      exact compatible

theorem generated_state_exact (s : State n) (names : List Nat)
    (assignment : Fin n → Comp Common.model) (lower upper : Comp Common.model) :
    All Common.model (extend lower upper assignment)
      (s.atoms.map (PresenceNormalForm.Atom.rename shift) ++
        CommonRoleCandidateConstraints.generate (slots names)) ↔
      All Common.model assignment s.atoms ∧
        (names = [] ∨ Common.Subtype lower.1 upper.1) := by
  rw [PresenceNormalForm.all_append, PresenceNormalForm.all_rename,
    CommonRoleCandidateConstraints.generate_exact, compatible_exact]
  rfl

/-- Every original occurrence is used by the real coalescer; arbitrary,
possibly unequal endpoints are retained, not replaced by a midpoint. -/
theorem merged_binding_exact (names : List Nat) (name : Nat) (member : name ∈ names)
    (assignment : Fin n → Comp Common.model) (lower upper actual : Common.Ty) :
    CommonRoleIntervals.Fits
      (CommonRoleIntervalGeneration.meaning
        (extend (Comp.pure Common.model lower) (Comp.pure Common.model upper) assignment)
        (CommonRoleCandidateConstraints.arguments (slots names) name)) actual ↔
      CommonRoleIntervals.Fits (lower, upper) actual := by
  rw [CommonRoleIntervalGeneration.meaning, CommonRoleIntervals.fits_coalesce]
  simp only [List.forall_mem_map, CommonRoleCandidateConstraints.arguments]
  constructor
  · intro all
    exact all (0, 1) (bounds_present names name member)
  · intro fit pair included
    rw [bounds_slots names name pair included]
    exact fit

/-- Concrete obstruction to erasing the new constraints. The old state is
satisfied, but the actual generated lower=int/upper=str capture is not. -/
theorem open_capture_not_noop :
    ¬ All Common.model
      (extend (Comp.pure Common.model (.base .int))
        (Comp.pure Common.model (.base .str)) (fun i : Fin 0 => Fin.elim0 i))
      ((State.empty (n := 0)).atoms.map (PresenceNormalForm.Atom.rename shift) ++
        CommonRoleCandidateConstraints.generate (slots [0])) := by
  rw [generated_state_exact]
  intro h
  have subtype : Common.Subtype (.base .int) (.base .str) := by simpa [Comp.pure, Common.model] using h.2
  have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp subtype
  cases impossible

end Yulang.CommonRoleOpenConstraints
