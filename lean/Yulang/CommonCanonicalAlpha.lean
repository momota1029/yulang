import Yulang.CommonCanonicalInterface

/-!
# Finite alpha-canonical codes for common constructor families

Shared type parameters are renamed simultaneously by an explicitly invertible
finite renaming. Alpha equivalence is defined independently through all common
type and row assignments. The encoder enumerates the finite renamings, applies
the proved constructor/lattice encoder, and chooses the least complete code.
No semantic equality oracle, typing derivation or solver witness is a parameter
of the executable encoder.

This is a reference algorithm for the finite `Form` grammar. It keeps the same
number of generalized slots and the same shared row IDs. It does not perform
polarity-based parameter elimination, identify weak/generalized parameters,
rename row variables or canonicalize arbitrary regular interfaces.
-/

namespace Yulang.CommonCanonicalAlpha

open ProducerCanonicalOpen (Expr Atom)
open CommonCanonicalInterface (Form Code Equivalent encode)

variable {n m k : Nat}

def renameAtom (rename : Fin n → Fin m) : Atom n → Atom m
  | .var index => .var (rename index)
  | .base scalar => .base scalar

def renameExpr (rename : Fin n → Fin m) : Expr n → Expr m
  | .atom entry => .atom (renameAtom rename entry)
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (renameExpr rename first) (renameExpr rename last)
  | .inter first last => .inter (renameExpr rename first) (renameExpr rename last)

def rename (mapping : Fin n → Fin m) : Form n → Form m
  | .scalar expression => .scalar (renameExpr mapping expression)
  | .pair first last => .pair (rename mapping first) (rename mapping last)
  | .required label payload => .required label (rename mapping payload)
  | .variant label payload => .variant label (rename mapping payload)
  | .arrow incoming outgoing input output =>
      .arrow incoming outgoing (renameExpr mapping input) (rename mapping output)

@[simp] theorem renameExpr_id (expression : Expr n) : renameExpr id expression = expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [renameExpr]

@[simp] theorem rename_id (expression : Form n) : rename id expression = expression := by
  induction expression <;> simp_all [rename]

theorem renameExpr_comp (first : Fin n → Fin m) (last : Fin m → Fin k) (expression : Expr n) :
    renameExpr last (renameExpr first expression) = renameExpr (last ∘ first) expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [renameExpr]

theorem rename_comp (first : Fin n → Fin m) (last : Fin m → Fin k) (expression : Form n) :
    rename last (rename first expression) = rename (last ∘ first) expression := by
  induction expression <;> simp_all [rename, renameExpr_comp]

theorem instantiate_renameExpr (mapping : Fin n → Fin m) (parameters : Fin m → Common.Ty)
    (expression : Expr n) :
    CommonCanonicalOpen.instantiate parameters (renameExpr mapping expression) =
      CommonCanonicalOpen.instantiate (parameters ∘ mapping) expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [renameExpr, CommonCanonicalOpen.instantiate]

theorem instantiate_rename (mapping : Fin n → Fin m) (rows : Nat → Common.Row)
    (parameters : Fin m → Common.Ty) (expression : Form n) :
    (rename mapping expression).instantiate rows parameters =
      expression.instantiate rows (parameters ∘ mapping) := by
  induction expression <;> simp_all [rename, Form.instantiate, instantiate_renameExpr]

theorem equivalent_rename {first last : Form n} (same : Equivalent first last)
    (mapping : Fin n → Fin m) : Equivalent (rename mapping first) (rename mapping last) := by
  intro rows parameters
  simpa only [instantiate_rename] using same rows (parameters ∘ mapping)

structure Permutation (n : Nat) where
  forward : Fin n → Fin n
  backward : Fin n → Fin n

def Permutation.Valid (permutation : Permutation n) : Prop :=
  (∀ index, permutation.backward (permutation.forward index) = index) ∧
    (∀ index, permutation.forward (permutation.backward index) = index)

instance (permutation : Permutation n) : Decidable permutation.Valid :=
  inferInstanceAs (Decidable ((∀ index, permutation.backward (permutation.forward index) = index) ∧
    (∀ index, permutation.forward (permutation.backward index) = index)))

def Permutation.identity (n : Nat) : Permutation n := ⟨id, id⟩
def Permutation.inverse (permutation : Permutation n) : Permutation n :=
  ⟨permutation.backward, permutation.forward⟩
def Permutation.then (first last : Permutation n) : Permutation n :=
  ⟨last.forward ∘ first.forward, first.backward ∘ last.backward⟩

theorem Permutation.identity_valid (n : Nat) : (identity n).Valid := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Permutation.inverse_valid {permutation : Permutation n} (valid : permutation.Valid) :
    permutation.inverse.Valid := ⟨valid.2, valid.1⟩

theorem Permutation.then_valid {first last : Permutation n}
    (before : first.Valid) (after : last.Valid) : (first.then last).Valid := by
  constructor <;> intro index
  · simp only [Permutation.then, Function.comp_apply, after.1, before.1]
  · simp only [Permutation.then, Function.comp_apply, before.2, after.2]

theorem rename_inverse {permutation : Permutation n} (valid : permutation.Valid) (expression : Form n) :
    rename permutation.backward (rename permutation.forward expression) = expression := by
  rw [rename_comp]
  have inverse : permutation.backward ∘ permutation.forward = id := funext valid.1
  rw [inverse, rename_id]

def AlphaEquivalent (first last : Form n) : Prop :=
  ∃ permutation : Permutation n, permutation.Valid ∧ Equivalent (rename permutation.forward first) last

theorem alpha_refl (expression : Form n) : AlphaEquivalent expression expression := by
  refine ⟨Permutation.identity n, Permutation.identity_valid n, ?_⟩
  simpa only [Permutation.identity, rename_id] using
    (show Equivalent expression expression from fun _ _ => Common.equivalent_refl _)

theorem alpha_symm {first last : Form n} (same : AlphaEquivalent first last) : AlphaEquivalent last first := by
  obtain ⟨permutation, valid, equivalent⟩ := same
  refine ⟨permutation.inverse, Permutation.inverse_valid valid, ?_⟩
  have reversed := equivalent_rename (CommonCanonicalInterface.equivalent_symm equivalent) permutation.backward
  simpa only [Permutation.inverse, rename_inverse valid] using reversed

theorem alpha_trans {first middle last : Form n}
    (before : AlphaEquivalent first middle) (after : AlphaEquivalent middle last) : AlphaEquivalent first last := by
  obtain ⟨firstPerm, firstValid, firstEq⟩ := before
  obtain ⟨lastPerm, lastValid, lastEq⟩ := after
  refine ⟨firstPerm.then lastPerm, Permutation.then_valid firstValid lastValid, ?_⟩
  have moved := equivalent_rename firstEq lastPerm.forward
  intro rows parameters
  have final := Common.equivalent_trans (moved rows parameters) (lastEq rows parameters)
  simpa only [Permutation.then, rename_comp] using final

/-- Existential instances are preserved in both directions, with one single
renaming for all occurrences of each generalized parameter. -/
theorem alpha_instances_exact {first last : Form n} (same : AlphaEquivalent first last)
    (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Equivalent (first.instantiate rows parameters) target) ↔
      ∃ parameters : Fin n → Common.Ty, Common.Equivalent (last.instantiate rows parameters) target := by
  have forward {first last : Form n} (same : AlphaEquivalent first last) :
      (∃ parameters : Fin n → Common.Ty, Common.Equivalent (first.instantiate rows parameters) target) →
        ∃ parameters : Fin n → Common.Ty, Common.Equivalent (last.instantiate rows parameters) target := by
    obtain ⟨permutation, valid, equivalent⟩ := same
    rintro ⟨parameters, witness⟩
    let renamed := parameters ∘ permutation.backward
    have assignment : renamed ∘ permutation.forward = parameters := by
      funext index
      simp only [renamed, Function.comp_apply, valid.1]
    have compared := equivalent rows renamed
    rw [instantiate_rename, assignment] at compared
    exact ⟨renamed, Common.equivalent_trans (Common.equivalent_symm compared) witness⟩
  exact ⟨forward same, forward (alpha_symm same)⟩

/-- An executable enumeration of every finite function. -/
def functions : (source target : Nat) → List (Fin source → Fin target)
  | 0, _ => [Fin.elim0]
  | source + 1, target => (List.finRange target).flatMap fun head =>
      (functions source target).map fun tail => Fin.cases head tail

theorem mem_functions (mapping : Fin n → Fin m) : mapping ∈ functions n m := by
  induction n with
  | zero =>
      have equal : mapping = Fin.elim0 := funext fun index => Fin.elim0 index
      simp [functions, equal]
  | succ n ih =>
      simp only [functions, List.mem_flatMap, List.mem_map]
      refine ⟨mapping 0, by simp, fun index => mapping index.succ, ih _, ?_⟩
      funext index
      refine Fin.cases ?_ (fun index => ?_) index <;> rfl

theorem functions_length (source target : Nat) : (functions source target).length = target ^ source := by
  induction source with
  | zero => simp [functions]
  | succ source ih =>
      simp [functions, List.length_flatMap, ih, List.map_const', List.sum_replicate_nat,
        Nat.pow_succ, Nat.mul_comm]

/-- The inverse is looked up, not independently enumerated. The fallback is
unreachable for a valid permutation, including the empty-domain case. -/
def inverseLookup (forward : Fin n → Fin n) (target : Fin n) : Fin n :=
  ((List.finRange n).find? fun source => decide (forward source = target)).getD target

theorem inverseLookup_exact (permutation : Permutation n) (valid : permutation.Valid) (target : Fin n) :
    inverseLookup permutation.forward target = permutation.backward target := by
  unfold inverseLookup
  cases found : (List.finRange n).find? (fun source => decide (permutation.forward source = target)) with
  | none =>
      have absent := (List.find?_eq_none.mp found) (permutation.backward target) (by simp)
      exact False.elim (absent (by simpa only [decide_eq_true_eq] using valid.2 target))
  | some source =>
      have accepted : decide (permutation.forward source = target) = true :=
        List.find?_some (p := fun candidate => decide (permutation.forward candidate = target)) found
      have equation : permutation.forward source = target := of_decide_eq_true accepted
      exact (valid.1 source).symm.trans (congrArg permutation.backward equation)

def permutations (n : Nat) : List (Permutation n) :=
  ((functions n n).map fun forward => Permutation.mk forward (inverseLookup forward)).filter fun permutation =>
    decide permutation.Valid

theorem mem_permutations (permutation : Permutation n) : permutation ∈ permutations n ↔ permutation.Valid := by
  simp only [permutations, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun member => member.2
  · intro valid
    refine ⟨?_, valid⟩
    apply List.mem_map.mpr
    refine ⟨permutation.forward, mem_functions _, ?_⟩
    have inverse : inverseLookup permutation.forward = permutation.backward :=
      funext (inverseLookup_exact permutation valid)
    rw [inverse]

/-- The reference pass checks one inverse lookup per forward candidate; it
does not take the Cartesian square of the finite function enumeration. -/
theorem permutations_length_le (n : Nat) : (permutations n).length ≤ n ^ n := by
  have bound := List.length_filter_le (fun permutation : Permutation n => decide permutation.Valid)
    ((functions n n).map fun forward => Permutation.mk forward (inverseLookup forward))
  simpa only [permutations, List.length_map, functions_length] using bound

def scalarKey (code : List (List (Atom n))) : List (List Nat) :=
  code.map (List.map ProducerCanonicalOpenClauses.atomKey)

private theorem atomKey_injective (first last : Atom n)
    (same : ProducerCanonicalOpenClauses.atomKey first = ProducerCanonicalOpenClauses.atomKey last) :
    first = last := by
  cases first with
  | var index =>
      cases last with
      | var other => exact congrArg Atom.var (Fin.eq_of_val_eq same)
      | base scalar => cases scalar <;> simp only [ProducerCanonicalOpenClauses.atomKey] at same <;> omega
  | base scalar =>
      cases last with
      | var index => cases scalar <;> simp only [ProducerCanonicalOpenClauses.atomKey] at same <;> omega
      | base other => cases scalar <;> cases other <;>
          simp only [ProducerCanonicalOpenClauses.atomKey] at same ⊢ <;> first | rfl | omega

private theorem scalarKey_injective (first last : List (List (Atom n)))
    (same : scalarKey first = scalarKey last) : first = last := by
  apply (List.map_inj_right (fun first last => (List.map_inj_right atomKey_injective).mp)).mp same

/-- Prefix lengths make the key injective without an external shape table. -/
def key : Code n → List (List Nat)
  | .scalar code => [0] :: scalarKey code
  | .pair first last => [1, (key first).length] :: (key first ++ key last)
  | .required label payload => [2, label] :: key payload
  | .variant label payload => [3, label] :: key payload
  | .arrow incoming outgoing input output =>
      [4, incoming, outgoing, input.length] :: (scalarKey input ++ key output)

theorem key_injective (first last : Code n) (same : key first = key last) : first = last := by
  induction first generalizing last with
  | scalar code =>
      cases last <;> simp [key] at same
      exact congrArg Code.scalar (scalarKey_injective _ _ same)
  | pair first rest ihf ihr =>
      cases last <;> simp [key] at same
      obtain ⟨lengths, joined⟩ := same
      obtain ⟨firsts, lasts⟩ := List.append_inj joined lengths
      rw [ihf _ firsts, ihr _ lasts]
  | required label payload ih =>
      cases last <;> simp [key] at same
      obtain ⟨rfl, payloads⟩ := same
      rw [ih _ payloads]
  | variant label payload ih =>
      cases last <;> simp [key] at same
      obtain ⟨rfl, payloads⟩ := same
      rw [ih _ payloads]
  | arrow incoming outgoing input output ih =>
      cases last <;> simp [key] at same
      obtain ⟨⟨rfl, rfl, lengths⟩, joined⟩ := same
      obtain ⟨inputs, outputs⟩ := List.append_inj joined (by simpa [scalarKey] using lengths)
      rw [scalarKey_injective _ _ inputs, ih _ outputs]

def lesser (first last : Code n) : Code n := if key first ≤ key last then first else last

private theorem lesser_mem (first last : Code n) : lesser first last = first ∨ lesser first last = last := by
  unfold lesser
  split <;> simp

private theorem lesser_le_first (first last : Code n) : key (lesser first last) ≤ key first := by
  unfold lesser
  split
  · exact List.le_refl _
  · rename_i greater
    exact (List.le_total (key first) (key last)).resolve_left greater

private theorem lesser_le_last (first last : Code n) : key (lesser first last) ≤ key last := by
  unfold lesser
  split
  · assumption
  · exact List.le_refl _

def least (initial : Code n) : List (Code n) → Code n
  | [] => initial
  | first :: rest => least (lesser initial first) rest

private theorem least_mem (initial : Code n) (list : List (Code n)) : least initial list ∈ initial :: list := by
  induction list generalizing initial with
  | nil => simp [least]
  | cons first rest ih =>
      have next := ih (lesser initial first)
      change least (lesser initial first) rest ∈ initial :: first :: rest
      rcases List.mem_cons.mp next with equal | member
      · rcases lesser_mem initial first with left | right
        · exact List.mem_cons.mpr (.inl (equal.trans left))
        · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl (equal.trans right))))
      · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr member)))

private theorem least_le (initial : Code n) (list : List (Code n)) :
    ∀ candidate ∈ initial :: list, key (least initial list) ≤ key candidate := by
  induction list generalizing initial with
  | nil =>
      intro candidate member
      have equal : candidate = initial := by simpa using member
      rw [equal]
      exact List.le_refl _
  | cons first rest ih =>
      intro candidate member
      have lower := ih (lesser initial first)
      rcases List.mem_cons.mp member with equal | member
      · rw [equal]
        exact List.le_trans (lower _ (by simp)) (lesser_le_first initial first)
      · rcases List.mem_cons.mp member with equal | member
        · rw [equal]
          exact List.le_trans (lower _ (by simp)) (lesser_le_last initial first)
        · exact lower _ (by simp [member])

def orbit (expression : Form n) : List (Code n) :=
  (permutations n).map fun permutation => encode (rename permutation.forward expression)

theorem mem_orbit (expression : Form n) (code : Code n) : code ∈ orbit expression ↔
    ∃ permutation : Permutation n,
      permutation.Valid ∧ encode (rename permutation.forward expression) = code := by
  simp only [orbit, List.mem_map, mem_permutations]

def canonicalEncoding (expression : Form n) : Code n := least (encode expression) (orbit expression)

theorem canonicalEncoding_member (expression : Form n) : canonicalEncoding expression ∈ orbit expression := by
  have member := least_mem (encode expression) (orbit expression)
  rcases List.mem_cons.mp member with equal | present
  · rw [show canonicalEncoding expression = encode expression from equal]
    apply (mem_orbit expression _).mpr
    refine ⟨Permutation.identity n, Permutation.identity_valid n, ?_⟩
    simp [Permutation.identity]
  · exact present

theorem canonicalEncoding_le (expression : Form n) (code : Code n) (member : code ∈ orbit expression) :
    key (canonicalEncoding expression) ≤ key code :=
  least_le (encode expression) (orbit expression) code (by simp [member])

theorem alpha_orbit {first last : Form n} (same : AlphaEquivalent first last) :
    ∀ code, code ∈ orbit last → code ∈ orbit first := by
  obtain ⟨permutation, valid, equivalent⟩ := same
  intro code member
  obtain ⟨next, nextValid, rfl⟩ := (mem_orbit last code).mp member
  apply (mem_orbit first _).mpr
  refine ⟨permutation.then next, Permutation.then_valid valid nextValid, ?_⟩
  have moved := equivalent_rename equivalent next.forward
  have codes := (CommonCanonicalInterface.canonicalEncoding_exact _ _).mp moved
  simpa only [Permutation.then, rename_comp] using codes

theorem canonicalEncoding_alpha {first last : Form n} (same : AlphaEquivalent first last) :
    canonicalEncoding first = canonicalEncoding last := by
  apply key_injective
  apply List.le_antisymm
  · exact canonicalEncoding_le first _ (alpha_orbit same _ (canonicalEncoding_member last))
  · exact canonicalEncoding_le last _ (alpha_orbit (alpha_symm same) _ (canonicalEncoding_member first))

def normalize (expression : Form n) : Form n := (canonicalEncoding expression).readback

theorem normalize_alpha (expression : Form n) : AlphaEquivalent expression (normalize expression) := by
  obtain ⟨permutation, valid, exactCode⟩ := (mem_orbit expression _).mp (canonicalEncoding_member expression)
  refine ⟨permutation, valid, ?_⟩
  have same := CommonCanonicalInterface.equivalent_symm
    (CommonCanonicalInterface.normalize_equivalent (rename permutation.forward expression))
  simpa only [normalize, CommonCanonicalInterface.normalize, exactCode] using same

/-- Equality is modulo one simultaneous finite bijection of the generalized
type slots, followed by demand equality for every row/type assignment. -/
theorem canonicalEncoding_exact (first last : Form n) :
    AlphaEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last := by
  constructor
  · exact canonicalEncoding_alpha
  · intro equal
    have normal : normalize first = normalize last := congrArg Code.readback equal
    have left := normalize_alpha first
    rw [normal] at left
    exact alpha_trans left (alpha_symm (normalize_alpha last))

theorem normalize_exact (first last : Form n) : AlphaEquivalent first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg Code.readback (canonicalEncoding_alpha same)
  · intro equal
    have left := normalize_alpha first
    rw [equal] at left
    exact alpha_trans left (alpha_symm (normalize_alpha last))

theorem normalize_idempotent (expression : Form n) : normalize (normalize expression) = normalize expression :=
  (normalize_exact _ _).mp (alpha_symm (normalize_alpha expression))

theorem alpha_preserves_arrow_rows {incoming outgoing incoming' outgoing' : Nat}
    {input input' : Expr n} {output output' : Form n}
    (same : AlphaEquivalent (.arrow incoming outgoing input output) (.arrow incoming' outgoing' input' output')) :
    incoming = incoming' ∧ outgoing = outgoing' := by
  obtain ⟨permutation, _, equivalent⟩ := same
  exact CommonCanonicalInterface.equivalent_arrow_rows equivalent

namespace Examples

def swapTwo : Permutation 2 :=
  ⟨Fin.cases 1 (fun _ => 0), Fin.cases 1 (fun _ => 0)⟩

theorem swapTwo_valid : swapTwo.Valid := by decide +kernel

theorem renamed_arrow_same_code :
    canonicalEncoding (n := 2) (.arrow 3 7 (.atom (.var 0)) (.scalar (.atom (.var 1)))) =
      canonicalEncoding (.arrow 3 7 (.atom (.var 1)) (.scalar (.atom (.var 0)))) := by
  apply canonicalEncoding_alpha
  refine ⟨swapTwo, swapTwo_valid, ?_⟩
  intro rows parameters
  exact Common.equivalent_refl _

end Examples

end Yulang.CommonCanonicalAlpha
