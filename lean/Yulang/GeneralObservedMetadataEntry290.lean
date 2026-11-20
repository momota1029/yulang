import Yulang.GeneralObservedMetadataKeys290

/-! Explicit executable comparison of all three per-key inputs to the old
nominal translator. No extensional equality of catalogue functions is used. -/
namespace Yulang.GeneralObservedMetadataEntry290
open GeneralDeclarationPatterns (Constructors Constructor ParameterKind)
open GeneralCandidateInspection (Primitive)
open GeneralNominalInspection (Interpretation)
open GeneralRebaseReceiptCatalogue289 (signature signature_injective)

inductive PrimitiveCode
  | scalar (base : Inference.Base)
  | pair
  | emptyRecord
  | exactEmpty
  deriving DecidableEq, Repr

def primitiveCode : Primitive → PrimitiveCode
  | .scalar b => .scalar b
  | .pair => .pair
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty

theorem primitiveCode_injective {a b : Primitive} (h : primitiveCode a = primitiveCode b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

theorem option_primitiveCode_injective {a b : Option Primitive}
    (h : a.map primitiveCode = b.map primitiveCode) : a = b := by
  cases a with
  | none => cases b <;> cases h <;> rfl
  | some a =>
    cases b with
    | none => cases h
    | some b => exact congrArg some (primitiveCode_injective (Option.some.inj h))

structure Entry where
  constructor : Option (List ParameterKind × Nat)
  primitive : Option PrimitiveCode
  invariant : Bool
  deriving DecidableEq, Repr

def entry (c : Constructors) (i : Interpretation) (key : Nat) : Entry :=
  ⟨signature c key,(i.primitives key).map primitiveCode,i.invariantNominal key⟩

def EntryEqual (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (key : Nat) : Prop :=
  c key = d key ∧ i.primitives key = j.primitives key ∧
    i.invariantNominal key = j.invariantNominal key

theorem entry_exact (c : Constructors) (i : Interpretation) (d : Constructors)
    (j : Interpretation) (key : Nat) : entry c i key = entry d j key ↔ EntryEqual c i d j key := by
  constructor
  · intro eq
    exact ⟨signature_injective _ _ _ (congrArg Entry.constructor eq),
      option_primitiveCode_injective (congrArg Entry.primitive eq),
      congrArg Entry.invariant eq⟩
  · rintro ⟨one,two,three⟩
    unfold entry signature
    rw [one,two,three]

def LocalEqual (keys : List Nat) (c : Constructors) (i : Interpretation)
    (d : Constructors) (j : Interpretation) : Prop :=
  ∀ key ∈ keys, EntryEqual c i d j key

def agree (keys : List Nat) (c : Constructors) (i : Interpretation)
    (d : Constructors) (j : Interpretation) : Bool :=
  keys.all fun key => decide (entry c i key = entry d j key)

theorem agree_exact (keys : List Nat) (c : Constructors) (i : Interpretation)
    (d : Constructors) (j : Interpretation) : agree keys c i d j = true ↔ LocalEqual keys c i d j := by
  unfold agree LocalEqual
  simp only [List.all_eq_true,decide_eq_true_eq,entry_exact]

theorem LocalEqual.restrict {whole part : List Nat} {c d : Constructors} {i j : Interpretation}
    (h : LocalEqual whole c i d j) (included : ∀ k ∈ part, k ∈ whole) :
    LocalEqual part c i d j := fun key found => h key (included key found)

theorem agree_refl (keys : List Nat) (c : Constructors) (i : Interpretation) :
    agree keys c i c i = true := (agree_exact ..).mpr (fun _ _ => ⟨rfl,rfl,rfl⟩)

end Yulang.GeneralObservedMetadataEntry290
