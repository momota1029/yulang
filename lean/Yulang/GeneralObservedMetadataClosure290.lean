import Yulang.GeneralObservedMetadataScope290

/-! Exact missing assumptions between a finite certificate and global old
Metadata. These off-scope hypotheses are independent of its success. -/
namespace Yulang.GeneralObservedMetadataClosure290
open GeneralDeclarations (Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralObservedMetadataScope290 (certify good_exact)
open GeneralObservedMetadataEntry290 (LocalEqual)
open GeneralObservedMetadataLocal290 (PrimitiveOKAt LocalPrimitiveOK metadata_restricts)

def OffScope (keys : List Nat) (r : Registry) (context : Context) : Prop :=
  (∀ key ∉ keys, r.constructors key = context.state.constructors key) ∧
  (∀ key ∉ keys, PrimitiveOKAt context.state.constructors context.interpretation key)

theorem metadata_iff (keys : List Nat) (r : Registry) (context : Context) :
    Metadata r context ↔
      certify keys r.constructors context.interpretation
        context.state.constructors context.interpretation = .good ∧ OffScope keys r context := by
  constructor
  · intro valid
    refine ⟨(good_exact ..).mpr (metadata_restricts r context valid keys), ?_⟩
    refine ⟨fun n _ => congrFun valid.1 n,?_⟩
    rw [← valid.1]
    exact fun n _ => valid.2 n
  · rintro ⟨verified, outside⟩
    have localMetadata := (good_exact ..).mp verified
    have fullConstructorAgreement : r.constructors = context.state.constructors := by
      funext key
      by_cases covered : key ∈ keys
      · exact (localMetadata.1 key covered).1
      · exact outside.1 key covered
    refine ⟨fullConstructorAgreement,?_⟩
    rw [fullConstructorAgreement]
    intro key
    by_cases covered : key ∈ keys
    · exact localMetadata.2 key covered
    · exact outside.2 key covered

theorem residual_constructor_needed {keys : List Nat} {r : Registry} {ctx : Context}
    {key : Nat} (different : r.constructors key ≠ ctx.state.constructors key) :
    ¬ OffScope keys r ctx ∨ key ∈ keys := by
  by_cases seen : key ∈ keys
  · exact Or.inr seen
  · exact Or.inl (fun rest => different (rest.1 key seen))

theorem offscope_from_common_default (keys : List Nat) (r : Registry) (ctx : Context)
    (defaultTable : GeneralDeclarationPatterns.Constructors)
    (left : ∀ key ∉ keys, r.constructors key = defaultTable key)
    (right : ∀ key ∉ keys, ctx.state.constructors key = defaultTable key)
    (primitiveSupport : ∀ key p, ctx.interpretation.primitives key = some p → key ∈ keys) :
    OffScope keys r ctx :=
  ⟨fun key h => (left key h).trans (right key h).symm,
   fun key h _ p => (h (primitiveSupport key _ p)).elim⟩

end Yulang.GeneralObservedMetadataClosure290
