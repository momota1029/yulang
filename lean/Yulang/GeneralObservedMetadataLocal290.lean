import Yulang.GeneralObservedMetadataEntry290

/-! Compatibility at queried keys is stronger than saying that two inputs
agree: both inputs could be equal and locally malformed. -/
namespace Yulang.GeneralObservedMetadataLocal290
open GeneralDeclarationPatterns (Constructors Constructor)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCandidates (Context Metadata)

def PrimitiveOKAt (c : Constructors) (i : Interpretation) (key : Nat) : Prop :=
  ∀ p, i.primitives key = some p →
    ∃ d, c key = some d ∧ d.parameters = p.parameters

def primitiveOKAt (c : Constructors) (i : Interpretation) (key : Nat) : Bool :=
  match i.primitives key with
  | none => true
  | some p =>
    match c key with
    | none => false
    | some d => decide (d.parameters = p.parameters)

theorem primitiveOKAt_exact (c : Constructors) (i : Interpretation) (key : Nat) :
    primitiveOKAt c i key = true ↔ PrimitiveOKAt c i key := by
  unfold primitiveOKAt PrimitiveOKAt
  cases hp : i.primitives key with
  | none => simp
  | some p =>
    cases hc : c key with
    | none => simp
    | some d => simp

def LocalPrimitiveOK (keys : List Nat) (c : Constructors) (i : Interpretation) : Prop :=
  ∀ key ∈ keys, PrimitiveOKAt c i key

def primitiveOK (keys : List Nat) (c : Constructors) (i : Interpretation) : Bool :=
  keys.all (primitiveOKAt c i)

theorem primitiveOK_exact (keys : List Nat) (c : Constructors) (i : Interpretation) :
    primitiveOK keys c i = true ↔ LocalPrimitiveOK keys c i := by
  simp only [primitiveOK,LocalPrimitiveOK,List.all_eq_true,primitiveOKAt_exact]

theorem metadata_restricts (r : GeneralDeclarations.Registry) (context : Context)
    (valid : Metadata r context) (keys : List Nat) :
    GeneralObservedMetadataEntry290.LocalEqual keys r.constructors context.interpretation
      context.state.constructors context.interpretation ∧
    LocalPrimitiveOK keys context.state.constructors context.interpretation := by
  refine ⟨fun key _ => ⟨congrFun valid.1 key,rfl,rfl⟩,?_⟩
  rw [← valid.1]
  exact fun key _ => valid.2 key

end Yulang.GeneralObservedMetadataLocal290
