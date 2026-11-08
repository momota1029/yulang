import Yulang.CommonRoleSettledSyntax
import Yulang.CommonRigidHeadInspection

/-! The original ordinary state has a disjoint namespace. A fresh slot 0
represents the entire captured payload; old slots are shifted by Fin.succ.
The fragment has no source variables shared between settled type graphs and
this auxiliary ordinary component. It admits every atom of the existing
family solver grammar in that component. Self and cross checks are generated
by the real candidate generator, even though they are reflexive here. -/
namespace Yulang.CommonRoleSettledConstraints
open CommonRoleSettledSyntax
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All)

structure State (n : Nat) where
  atoms : List (PresenceNormalForm.Atom (Fin n))
  child : PresenceGeneratedChildGrammar.GoodAtoms atoms
  width : PresenceGeneratedWidth.WidthAtoms atoms
  rows : PresenceSourceConstraintSupport.GoodAtoms atoms

def State.empty : State n := ⟨[], (by intro a h; cases h),
  (by intro a b h; cases h), (by intro a h; cases h)⟩

def State.Models (s : State n) : Prop := ∃ assignment, All Common.model assignment s.atoms

/-- All captures in a unary head are at the same leaf. Repeated names retain
all occurrences in the generated self/cross constraints. -/
def slots (names : List Nat) : CommonRoleCandidateConstraints.Bindings (n + 1) := names.map (fun name => (name, (0, 0)))

theorem bounds_slots (names : List Nat) (name : Nat) (pair : Fin (n + 1) × Fin (n + 1))
    (h : pair ∈ CommonRoleCandidateConstraints.bounds (slots names) name) : pair = (0, 0) := by
  obtain ⟨⟨key, pair'⟩, member, found⟩ := List.mem_filterMap.mp h
  obtain ⟨original, _, equal⟩ := List.mem_map.mp member
  cases equal
  split at found <;> simp_all

theorem captures_compatible (names : List Nat) (assignment : Fin (n + 1) → Comp Common.model) :
    CommonRoleCandidateConstraints.Compatible (slots names) assignment := by
  intro name _ first present last included
  rw [bounds_slots names name first present, bounds_slots names name last included]
  exact Common.subtype_refl _

/-- Actual semantic payloads, including regular Common graphs, can always
occupy the fresh slot. Original source slots and rows are preserved literally. -/
theorem generated_state_exact (s : State n) (names : List Nat)
    (assignment : Fin n → Comp Common.model) (payload : Comp Common.model) :
    All Common.model (Fin.cases payload assignment)
      (s.atoms.map (PresenceNormalForm.Atom.rename Fin.succ) ++ CommonRoleCandidateConstraints.generate (slots names)) ↔
      All Common.model assignment s.atoms := by
  rw [PresenceNormalForm.all_append, PresenceNormalForm.all_rename, CommonRoleCandidateConstraints.generate_exact]
  simp only [captures_compatible, and_true]
  rfl

/-- Known rigid disjointness may eliminate a candidate before K2. At a
regular leaf only the already exposed constructor is compared; its body is
never recursively opened. Unknown structure is not a mismatch. -/
def rigid : Pattern → Ty → Bool
  | .bind _ _, _ => true
  | _, .unknown => true
  | .atom a, .atom b => decide (a = b)
  | .wrap c p, .wrap d t =>
      decide (c = d) && (if (Ty.wrap d t).regular then true else rigid p t)
  | .wrap c _, .variantLoop tag => decide (c = .variant tag)
  | .wrap c _, .recordLoop label => decide (c = .record label)
  | _, _ => false

inductive Rigid : Pattern → Ty → Prop where
  | bind : Rigid (.bind first more) t
  | unknown : Rigid p .unknown
  | atom : Rigid (.atom a) (.atom a)
  | wrapRegular : (Ty.wrap c t).Regular → Rigid (.wrap c p) (.wrap c t)
  | wrap : ¬ (Ty.wrap c t).Regular → Rigid p t → Rigid (.wrap c p) (.wrap c t)
  | variantLoop : Rigid (.wrap (.variant tag) p) (.variantLoop tag)
  | recordLoop : Rigid (.wrap (.record label) p) (.recordLoop label)

theorem rigid_sound (p : Pattern) (t : Ty) (h : rigid p t = true) : Rigid p t := by
  induction p generalizing t with
  | bind => exact .bind
  | atom a =>
      cases t <;> simp [rigid] at h
      · exact .unknown
      · subst a; exact .atom
  | wrap c p ih =>
      cases t with
      | unknown => exact .unknown
      | atom a => simp [rigid] at h
      | wrap d t =>
          have parts := Bool.and_eq_true_iff.mp h
          have same : c = d := by simpa using parts.1
          subst d
          by_cases cyclic : (Ty.wrap c t).regular = true
          · exact .wrapRegular ((regular_exact _).mp cyclic)
          · exact .wrap (mt (regular_exact _).mpr cyclic) (ih t (by simpa [cyclic] using parts.2))
      | variantLoop tag => have same : c = .variant tag := by simpa [rigid] using h
                           subst c; exact .variantLoop
      | recordLoop label => have same : c = .record label := by simpa [rigid] using h
                            subst c; exact .recordLoop

theorem rigid_complete (h : Rigid p t) : rigid p t = true := by
  induction h with
  | bind | atom | variantLoop | recordLoop => simp [rigid]
  | @unknown pat => cases pat <;> rfl
  | wrapRegular cyclic => simp [rigid, (regular_exact _).mpr cyclic]
  | wrap finite _ ih => simp [rigid, regular_false finite, ih]

theorem rigid_exact (p : Pattern) (t : Ty) : rigid p t = true ↔ Rigid p t :=
  ⟨rigid_sound p t, rigid_complete⟩

/-- Rigid clashes compile to an ordinary inconsistent atom. This avoids
turning a dead unrelated head into a K2 veto. -/
def clash : List (PresenceNormalForm.Atom (Fin (n + 1))) := [.tyLe (.base .int) (.base .str)]

theorem clash_impossible (assignment : Fin (n + 1) → Comp Common.model) :
    ¬ All Common.model assignment clash := by
  intro h
  have bad := h (.tyLe (.base .int) (.base .str)) (by simp [clash])
  have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp bad
  cases impossible

theorem clash_grammar : PresenceGeneratedChildGrammar.GoodAtoms (clash (n := n)) ∧
    PresenceGeneratedWidth.WidthAtoms (clash (n := n)) ∧
    PresenceSourceConstraintSupport.GoodAtoms (clash (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member; simp only [clash, List.mem_singleton] at member; subst atom; trivial
  · intro source target member tail needed
    simp only [clash, List.mem_singleton] at member
    cases member; cases needed
  · intro atom member; simp only [clash, List.mem_singleton] at member; subst atom; trivial

def original (s : State n) (p : Pattern) (t : Ty) : List (PresenceNormalForm.Atom (Fin (n + 1))) :=
  s.atoms.map (PresenceNormalForm.Atom.rename Fin.succ) ++ if rigid p t then [] else clash

theorem original_grammar (s : State n) (p : Pattern) (t : Ty) :
    PresenceGeneratedChildGrammar.GoodAtoms (original s p t) ∧
    PresenceGeneratedWidth.WidthAtoms (original s p t) ∧
    PresenceSourceConstraintSupport.GoodAtoms (original s p t) := by
  unfold original
  split
  · simpa using And.intro (s.child.rename Fin.succ) (And.intro (s.width.rename Fin.succ) (s.rows.rename Fin.succ))
  · exact ⟨(s.child.rename Fin.succ).append clash_grammar.1,
      (s.width.rename Fin.succ).append clash_grammar.2.1,
      (s.rows.rename Fin.succ).append clash_grammar.2.2⟩

def propagate (s : State n) (p : Pattern) (t : Ty) : Bool :=
  !(CommonRoleCandidateConstraints.solve (original s p t) (slots (n := n) p.names)).isEmpty

/-- Quantification is over models of generated ordinary constraints only.
No head substitution is searched for or existentially supplied. -/
theorem propagate_exact (s : State n) (p : Pattern) (t : Ty) :
    propagate s p t = true ↔ s.Models ∧ Rigid p t := by
  have grammar := original_grammar s p t
  have empty := CommonRoleCandidateConstraints.solve_empty_exact (original s p t) (slots (n := n) p.names)
    grammar.1 grammar.2.1 grammar.2.2
  have models : (∃ assignment, All Common.model assignment (original s p t) ∧
      CommonRoleCandidateConstraints.Compatible (slots p.names) assignment) ↔ s.Models ∧ Rigid p t := by
    constructor
    · rintro ⟨assignment, model, _⟩
      rw [original, PresenceNormalForm.all_append] at model
      have ok : rigid p t = true := by
        cases h : rigid p t
        · exact False.elim (clash_impossible assignment (by simpa [h] using model.2))
        · rfl
      exact ⟨⟨assignment ∘ Fin.succ, (PresenceNormalForm.all_rename ..).mp model.1⟩,
        (rigid_exact p t).mp ok⟩
    · rintro ⟨⟨assignment, model⟩, ok⟩
      let expanded : Fin (n + 1) → Comp Common.model := Fin.cases (Comp.pure Common.model (.base .int)) assignment
      refine ⟨expanded, ?_, captures_compatible _ _⟩
      simp only [original, (rigid_exact p t).mpr ok, ite_true, List.append_nil,
        PresenceNormalForm.all_rename]
      exact model
  rw [models] at empty
  unfold propagate
  cases result : CommonRoleCandidateConstraints.solve (original s p t) (slots (n := n) p.names) with
  | nil =>
      have no := empty.mp result
      simp only [List.isEmpty, Bool.not_true, Bool.false_eq_true, false_iff]
      exact no
  | cons first rest =>
      have h : s.Models ∧ Rigid p t := by
        classical
        by_cases h : s.Models ∧ Rigid p t
        · exact h
        · have := empty.mpr h
          simp [result] at this
      simp [h]

/-- Repeated equal captures normalize to the original two endpoints. This
checks every occurrence, not just the first lookup. -/
theorem merged_captures_exact (count : Nat) (positive : 0 < count)
    (payload actual : Common.Ty) :
    CommonRoleIntervals.Fits
      (CommonRoleIntervals.coalesce (List.replicate count (payload, payload))) actual ↔
      CommonRoleIntervals.Fits (payload, payload) actual := by
  rw [CommonRoleIntervals.fits_coalesce]
  constructor
  · intro h; apply h (payload, payload); simp [List.mem_replicate, Nat.ne_of_gt positive]
  · intro h interval member
    have same : interval = (payload, payload) := (List.mem_replicate.mp member).2
    simpa [same] using h
/-- Direct bridge for the ACTUAL generated occurrence list of a head name.
The merged interval has exactly the original captured singleton meaning. -/
theorem merged_binding_exact (names : List Nat) (name : Nat) (member : name ∈ names)
    (assignment : Fin n → Comp Common.model) (payload actual : Common.Ty) :
    CommonRoleIntervals.Fits
      (CommonRoleIntervalGeneration.meaning (Fin.cases (Comp.pure Common.model payload) assignment)
        (CommonRoleCandidateConstraints.arguments (slots names) name)) actual ↔
      CommonRoleIntervals.Fits (payload, payload) actual := by
  rw [CommonRoleIntervalGeneration.meaning, CommonRoleIntervals.fits_coalesce]
  simp only [List.forall_mem_map, CommonRoleCandidateConstraints.arguments]
  have present : (0, 0) ∈ CommonRoleCandidateConstraints.bounds (slots (n := n) names) name := by
    apply List.mem_filterMap.mpr
    refine ⟨(name, (0, 0)), List.mem_map.mpr ⟨name, member, rfl⟩, ?_⟩
    simp
  constructor
  · intro all
    exact all (0, 0) present
  · intro fit pair included
    rw [bounds_slots names name pair included]
    exact fit

end Yulang.CommonRoleSettledConstraints
