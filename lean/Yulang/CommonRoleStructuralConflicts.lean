import Yulang.CommonRoleConflictFilteredInference

/-! Rigid outer-head conflict certificates for real ordinary terms.
Payloads and rows may contain arbitrary variables. This is not a complete
structural subtype or satisfiability procedure. -/
namespace Yulang.CommonRoleStructuralConflicts
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRigidHeadInspection (Head head rigid)
open CommonRoleSettledConstraints (State)

def staticHead : TyTerm α → Option Head
  | .var _ | .union _ _ | .inter _ _ => none
  | .base b => some (.base b)
  | .bottom => some .bottom
  | .top => some .top
  | .pair _ _ => some .pair
  | .arrow _ _ _ _ => some .arrow
  | .emptyRecord | .exactEmpty | .required _ _ | .record _ _ _ | .recordDefault _ _ _ => some .records
  | .variant tag _ => some (.variant tag)

theorem staticHead_sound (t : TyTerm α) (h : staticHead t = some tag)
    (a : α → Comp Common.model) :
    rigid (t.eval Common.model a) = true ∧ head (t.eval Common.model a) = tag := by
  cases t <;> simp_all [staticHead, TyTerm.eval, Common.model, Common.pair,
    Common.arrow, Common.emptyRecord, Common.exactEmpty, Common.required,
    Common.record, Common.recordDefault, Common.variant, rigid, head]

def Mismatch (l r : TyTerm α) : Prop :=
  ∃ lh rh, staticHead l = some lh ∧ staticHead r = some rh ∧
    lh ≠ .bottom ∧ rh ≠ .top ∧ lh ≠ rh

def mismatch (l r : TyTerm α) : Bool :=
  match staticHead l, staticHead r with
  | some lh, some rh => decide (lh ≠ .bottom ∧ rh ≠ .top ∧ lh ≠ rh)
  | _, _ => false

theorem mismatch_exact (l r : TyTerm α) : mismatch l r = true ↔ Mismatch l r := by
  unfold mismatch Mismatch
  cases staticHead l <;> cases staticHead r <;> simp

theorem mismatch_no_subtype (l r : TyTerm α) (h : Mismatch l r)
    (a : α → Comp Common.model) : ¬ Common.Subtype (l.eval Common.model a) (r.eval Common.model a) := by
  obtain ⟨lh,rh,hl,hr,hb,ht,hd⟩ := h
  obtain ⟨rl,el⟩ := staticHead_sound l hl a
  obtain ⟨rr,er⟩ := staticHead_sound r hr a
  exact CommonRigidHeadInspection.rigid_mismatch rl rr (by simpa [el] using hb)
    (by simpa [er] using ht) (by simpa [el,er] using hd)

def direct : Atom α → Bool
  | .tyLe l r => mismatch l r
  | .rowLe _ _ => false

def through [DecidableEq α] : Atom α → Atom α → Bool
  | .tyLe l (.var i), .tyLe (.var j) r => decide (i = j) && mismatch l r
  | _, _ => false

/-- An independent finite certificate, with arbitrary structural payloads. -/
inductive Certificate (atoms : List (Atom α)) : Prop where
  | direct : Atom.tyLe l r ∈ atoms → Mismatch l r → Certificate atoms
  | through : Atom.tyLe l (.var i) ∈ atoms → Atom.tyLe (.var i) r ∈ atoms →
      Mismatch l r → Certificate atoms

def check [DecidableEq α] (atoms : List (Atom α)) : Bool :=
  atoms.any direct || atoms.any (fun l => atoms.any (through l))

theorem direct_exact (x : Atom α) : direct x = true ↔
    ∃ l r, x = .tyLe l r ∧ Mismatch l r := by
  cases x with
  | rowLe => simp [direct]
  | tyLe l r =>
    simp only [direct, mismatch_exact]
    constructor
    · intro h; exact ⟨l,r,rfl,h⟩
    · rintro ⟨l',r',h,hm⟩; cases h; exact hm

theorem through_exact [DecidableEq α] (x y : Atom α) : through x y = true ↔
    ∃ l r i, x = .tyLe l (.var i) ∧ y = .tyLe (.var i) r ∧ Mismatch l r := by
  cases x with
  | rowLe => cases y <;> simp [through]
  | tyLe l mid =>
    cases mid <;> cases y <;> simp [through]
    case var.tyLe i mid r =>
      cases mid <;> simp [mismatch_exact]
      case var j =>
        constructor
        · rintro ⟨h, hm⟩; subst j; exact ⟨l,r,i,⟨rfl,rfl⟩,⟨rfl,rfl⟩,hm⟩
        · rintro ⟨l',r',i',⟨hl,hi⟩,⟨hj,hr⟩,hm⟩
          subst l'; subst r'; subst i'; subst j
          exact ⟨rfl,hm⟩

theorem check_exact [DecidableEq α] (atoms : List (Atom α)) :
    check atoms = true ↔ Certificate atoms := by
  simp only [check, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨x,hx,h⟩ | ⟨x,hx,y,hy,h⟩)
    · obtain ⟨l,r,rfl,hm⟩ := (direct_exact x).mp h
      exact .direct hx hm
    · obtain ⟨l,r,i,rfl,rfl,hm⟩ := (through_exact x y).mp h
      exact .through hx hy hm
  · intro h
    cases h with
    | direct hl hm => exact Or.inl ⟨_,hl,(direct_exact _).mpr ⟨_,_,rfl,hm⟩⟩
    | through hl hr hm => exact Or.inr ⟨_,hl,_,hr,(through_exact _ _).mpr ⟨_,_,_,rfl,rfl,hm⟩⟩

theorem certificate_no_model (atoms : List (Atom α)) (h : Certificate atoms)
    (a : α → Comp Common.model) : ¬ All Common.model a atoms := by
  intro models
  cases h with
  | direct hl hm => exact mismatch_no_subtype _ _ hm a (models _ hl)
  | through hl hr hm =>
    exact mismatch_no_subtype _ _ hm a (Common.subtype_trans (models _ hl) (models _ hr))

theorem checked_no_model [DecidableEq α] (atoms : List (Atom α)) (h : check atoms = true)
    (a : α → Comp Common.model) : ¬ All Common.model a atoms :=
  certificate_no_model atoms ((check_exact atoms).mp h) a

def prune (states : List (State n)) : List (State n) :=
  states.filter fun s => !check s.atoms

theorem prune_models (states : List (State n)) (a : Fin n → Comp Common.model) :
    (∃ s ∈ prune states, All Common.model a s.atoms) ↔
      ∃ s ∈ states, All Common.model a s.atoms := by
  constructor
  · rintro ⟨s,hs,hm⟩
    exact ⟨s,(List.mem_filter.mp hs).1,hm⟩
  · rintro ⟨s,hs,hm⟩
    refine ⟨s,List.mem_filter.mpr ⟨hs,?_⟩,hm⟩
    cases hc : check s.atoms
    · rfl
    · exact False.elim (checked_no_model s.atoms hc a hm)

/-- Arbitrary pair payloads, including variables or bottom, retain their outer head. -/
theorem pair_scalar_conflict (l r : TyTerm α) (b : Inference.Base) :
    Mismatch (.pair l r) (.base b) := by
  exact (mismatch_exact _ _).mp (by rfl)

theorem pair_slot_scalar_no_model (l r : TyTerm α) (i : α) (b : Inference.Base)
    (a : α → Comp Common.model) :
    ¬ All Common.model a [.tyLe (.pair l r) (.var i), .tyLe (.var i) (.base b)] := by
  apply certificate_no_model
  exact Certificate.through (i := i) (by simp) (by simp) (pair_scalar_conflict l r b)

theorem bottom_not_mismatch (r : TyTerm α) : mismatch .bottom r = false := by
  cases r <;> simp [mismatch,staticHead]

theorem top_target_not_mismatch (l : TyTerm α) : mismatch l .top = false := by
  cases l <;> simp [mismatch,staticHead]

end Yulang.CommonRoleStructuralConflicts
