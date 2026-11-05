import Yulang.StructuralDecisions
import Yulang.SemilinearAutomata
import Yulang.RecursiveRows

/-!
# Finite-key semilinear rows and ground structural comparison

A row is a finite list of operation keys paired with finite semilinear
presentations. Each presentation may denote infinitely many signed weights.
Repeated keys contribute their union; there is no first-key-wins convention.
Missing keys denote the empty set. Inclusion checks only the source's actual
key support and is exact over every key and every integer vector.

The structural checker uses this executable inclusion relation, so finite
ground value types may carry infinite recursive effect rows. This does not
infer unresolved value types or add recursive value types to StructuralBase.
-/

namespace Yulang.SemilinearRowAlgebra

open SemilinearWeights (Weight Semi Linear)

variable {n : Nat} {Key : Type}

abbrev Row (n : Nat) (Key : Type) := List (Key × Semi n)

def support (row : Row n Key) : List Key := row.map Prod.fst

def lookup [DecidableEq Key] : Row n Key → Key → Semi n
  | [], _ => []
  | (name, semi) :: rest, key =>
      if key = name then semi ++ lookup rest key else lookup rest key

def Meaning [DecidableEq Key] (row : Row n Key) (key : Key) (weight : Weight n) : Prop :=
  SemilinearWeights.Meaning (lookup row key) weight

@[simp] theorem meaning_empty [DecidableEq Key] (key : Key) (weight : Weight n) :
    ¬ Meaning ([] : Row n Key) key weight := by
  simp [Meaning, lookup]

theorem lookup_append [DecidableEq Key] (left right : Row n Key) (key : Key) :
    lookup (left ++ right) key = lookup left key ++ lookup right key := by
  induction left generalizing key with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, semi⟩
      by_cases equal : key = name <;> simp [lookup, equal, ih, List.append_assoc]

theorem meaning_append [DecidableEq Key] (left right : Row n Key) (key : Key) (weight : Weight n) :
    Meaning (left ++ right) key weight ↔ Meaning left key weight ∨ Meaning right key weight := by
  simp only [Meaning, lookup_append, SemilinearWeights.meaning_append, SemilinearWeights.Join]

theorem meaning_cons [DecidableEq Key] (name : Key) (semi : Semi n) (rest : Row n Key)
    (key : Key) (weight : Weight n) :
    Meaning ((name, semi) :: rest) key weight ↔
      (key = name ∧ SemilinearWeights.Meaning semi weight) ∨ Meaning rest key weight := by
  by_cases equal : key = name
  · simp [Meaning, lookup, equal, SemilinearWeights.meaning_append, SemilinearWeights.Join]
  · simp [Meaning, lookup, equal]

theorem lookup_empty_outside_support [DecidableEq Key] (row : Row n Key) (key : Key)
    (absent : key ∉ support row) : lookup row key = [] := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, semi⟩
      have different : key ≠ name := by
        intro equal
        exact absent (by simp [support, equal])
      have missing : key ∉ support rest := fun member => absent (by simp [support] at member ⊢; exact Or.inr member)
      simp only [lookup, ite_eq_right different, ih missing]

theorem meaning_key_mem [DecidableEq Key] (row : Row n Key) (key : Key) (weight : Weight n)
    (member : Meaning row key weight) : key ∈ support row := by
  by_cases present : key ∈ support row
  · exact present
  · have empty := lookup_empty_outside_support row key present
    simp only [Meaning, empty, SemilinearWeights.meaning_nil] at member

def Included [DecidableEq Key] (source target : Row n Key) : Prop :=
  ∀ key weight, Meaning source key weight → Meaning target key weight

theorem included_refl [DecidableEq Key] (row : Row n Key) : Included row row := fun _ _ member => member

theorem included_trans [DecidableEq Key] {first second third : Row n Key}
    (left : Included first second) (right : Included second third) : Included first third :=
  fun key weight member => right key weight (left key weight member)

/-- No enumeration of the type of keys is required. Duplicate source keys
repeat an exact check and do not change its meaning. -/
def checkSubset [DecidableEq Key] (source target : Row n Key) : Bool :=
  (support source).all fun key => SemilinearAutomata.checkSubset (lookup source key) (lookup target key)

theorem checkSubset_exact [DecidableEq Key] (source target : Row n Key) :
    checkSubset source target = true ↔ Included source target := by
  simp only [checkSubset, List.all_eq_true, SemilinearAutomata.checkSubset_exact]
  constructor
  · intro checked key weight member
    exact checked key (meaning_key_mem source key weight member) weight member
  · intro included key _ weight member
    exact included key weight member

theorem checkSubset_rejects [DecidableEq Key] (source target : Row n Key) :
    checkSubset source target = false ↔
      ∃ key weight, Meaning source key weight ∧ ¬ Meaning target key weight := by
  simp only [checkSubset, List.all_eq_false, ← Bool.eq_false_iff, SemilinearAutomata.checkSubset_rejects]
  constructor
  · rintro ⟨key, _, weight, member, absent⟩
    exact ⟨key, weight, member, absent⟩
  · rintro ⟨key, weight, member, absent⟩
    exact ⟨key, meaning_key_mem source key weight member, weight, member, absent⟩

def checkEqual [DecidableEq Key] (left right : Row n Key) : Bool :=
  checkSubset left right && checkSubset right left

theorem checkEqual_exact [DecidableEq Key] (left right : Row n Key) :
    checkEqual left right = true ↔ ∀ key weight, Meaning left key weight ↔ Meaning right key weight := by
  simp only [checkEqual, Bool.and_eq_true, checkSubset_exact, Included]
  exact ⟨fun ⟨forward, backward⟩ key weight => ⟨forward key weight, backward key weight⟩,
    fun same => ⟨fun key weight => (same key weight).mp, fun key weight => (same key weight).mpr⟩⟩

def decode [DecidableEq Key] (row : Row n Key) : RecursiveRows.SetRow n Key :=
  fun occurrence => Meaning row occurrence.key occurrence.weights

theorem checkSubset_sets [DecidableEq Key] (source target : Row n Key) :
    checkSubset source target = true ↔ (RecursiveRows.algebra n Key).le (decode source) (decode target) := by
  rw [checkSubset_exact]
  constructor
  · intro included occurrence member
    exact included occurrence.key occurrence.weights member
  · intro included key weight member
    exact included ⟨key, weight⟩ member

theorem checkEqual_sets [DecidableEq Key] (left right : Row n Key) :
    checkEqual left right = true ↔ decode left = decode right := by
  rw [checkEqual_exact]
  constructor
  · intro same
    funext occurrence
    exact propext (same occurrence.key occurrence.weights)
  · intro same key weight
    have point := congrFun same (Directed.Occurrence.mk key weight)
    exact iff_of_eq point

theorem decode_empty [DecidableEq Key] :
    decode ([] : Row n Key) = (RecursiveRows.algebra n Key).empty := by
  funext occurrence
  apply propext
  simp [decode, Meaning, lookup, RecursiveRows.algebra]

theorem decode_append [DecidableEq Key] (left right : Row n Key) :
    decode (left ++ right) = (RecursiveRows.algebra n Key).join (decode left) (decode right) := by
  funext occurrence
  exact propext (meaning_append left right occurrence.key occurrence.weights)

instance weightDecidableEq : DecidableEq (Weight n) := fun left right =>
  if equal : ∀ coordinate, left coordinate = right coordinate then
    isTrue (funext equal)
  else isFalse (fun same => equal (congrFun same))

deriving instance DecidableEq for Linear

abbrev GroundType (n : Nat) (Key : Type) := StructuralBase.Ty (Row n Key)

def model (n : Nat) (Key : Type) [DecidableEq Key] : Inference.Model :=
  StructuralBase.model (Row n Key) [] List.append Included

/-- Ground value types are finite, while every latent row may contain an
unbounded semilinear set of protected and released occurrences. -/
def checkType [DecidableEq Key] (source target : GroundType n Key) : Bool :=
  StructuralDecisions.check checkSubset source target

theorem checkType_exact [DecidableEq Key] (source target : GroundType n Key) :
    checkType source target = true ↔ StructuralBase.Subtype Included source target :=
  StructuralDecisions.check_exact checkSubset checkSubset_exact
    (fun first second => included_trans first second) source target

theorem checkType_rejects [DecidableEq Key] (source target : GroundType n Key) :
    checkType source target = false ↔ ¬ StructuralBase.Subtype Included source target := by
  rw [← checkType_exact]
  cases checkType source target <;> simp

def equivalentType [DecidableEq Key] (left right : GroundType n Key) : Bool :=
  checkType left right && checkType right left

theorem equivalentType_exact [DecidableEq Key] (left right : GroundType n Key) :
    equivalentType left right = true ↔
      StructuralBase.Subtype Included left right ∧ StructuralBase.Subtype Included right left := by
  simp only [equivalentType, Bool.and_eq_true, checkType_exact]

end Yulang.SemilinearRowAlgebra
