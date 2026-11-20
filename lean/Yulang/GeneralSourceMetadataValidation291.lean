import Yulang.GeneralSourceMetadataLookup291

/-! A source validator: duplicate keys and incompatible primitive layouts
are independent constraints. Invariant qualifiers alone do not promise
materialization of any row-bearing layout. -/
namespace Yulang.GeneralSourceMetadataValidation291
open GeneralSourceMetadataRows291
open GeneralSourceMetadataLookup291 (locate projected present)
open GeneralCandidateInspection (PrimitivesCompatible)

def PrimitiveLayout (row : Row) : Prop :=
  ∀ p, row.classification.primitiveValue = some p →
    ∃ d, row.ctor = some d ∧ d.parameters = p.parameters

def layoutOK (row : Row) : Bool :=
  match row.classification.primitiveValue with
  | none => true
  | some p => match row.ctor with
    | none => false
    | some d => decide (d.parameters = p.parameters)

theorem layout_exact (row : Row) : layoutOK row = true ↔ PrimitiveLayout row := by
  unfold layoutOK PrimitiveLayout
  cases value : row.classification.primitiveValue with
  | none => simp
  | some p => cases row.ctor <;> simp

def Valid (s : Source) : Prop :=
  (s.rows.map Row.key).Nodup ∧ ∀ row ∈ s.rows, PrimitiveLayout row

def check (s : Source) : Bool :=
  decide (s.rows.map Row.key).Nodup && s.rows.all layoutOK

theorem check_exact (s : Source) : check s = true ↔ Valid s := by
  simp only [check,Valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,layout_exact]

theorem primitive_compatible (s : Source) (valid : Valid s) :
    PrimitivesCompatible (constructors s) (interpretation s).primitives := by
  intro key p found
  have values := projected s.fallback s.rows key
  change primitives s key = some p at found
  cases h : locate key s.rows with
  | none =>
    rw [h] at values
    have missing := congrArg (fun triple => triple.2.1) values
    change primitives s key = none at missing
    rw [found] at missing
    cases missing
  | some row =>
    rw [h] at values
    have ct := congrArg Prod.fst values
    have pc := congrArg (fun triple => triple.2.1) values
    change constructors s key = row.ctor at ct
    change primitives s key = row.classification.primitiveValue at pc
    obtain ⟨d,ctor,shape⟩ := valid.2 row (present h).1 p (pc.symm.trans found)
    exact ⟨d,ct.trans ctor,shape⟩

theorem checked_primitive (s : Source) (success : check s = true) :
    PrimitivesCompatible (constructors s) (interpretation s).primitives :=
  primitive_compatible s ((check_exact s).mp success)

end Yulang.GeneralSourceMetadataValidation291
