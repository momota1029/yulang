import Yulang.GeneralObservedMetadataPublic290

/-! Equality on a finite probe is globally complete only when independently
witnessed tables really have this common-default representation. -/
namespace Yulang.GeneralObservedMetadataOverlay290
open GeneralDeclarationPatterns (Constructor Constructors)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarations (Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralObservedMetadataClosure290 (OffScope metadata_iff offscope_from_common_default)
open GeneralObservedMetadataScope290 (certify)

def overlay {α : Type} (fallback : Nat → α) : List (Nat × α) → Nat → α
  | [], key => fallback key
  | (name,value) :: rest, key => if key = name then value else overlay fallback rest key

theorem default_outside {α : Type} (fallback : Nat → α) (data : List (Nat × α))
    (key : Nat) (outside : key ∉ data.map Prod.fst) : overlay fallback data key = fallback key := by
  induction data with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name,value⟩ := entry
    have away : key ≠ name := fun collision => outside (by simp [collision])
    have tail : key ∉ rest.map Prod.fst := fun occurs => outside (List.mem_cons_of_mem _ occurs)
    simp only [overlay,ite_eq_right away,ih tail]

structure Data where
  fallback : Constructors
  declared : List (Nat × Option Constructor)
  recorded : List (Nat × Option Constructor)
  primitives : List (Nat × Option Primitive)

def Data.extended (data : Data) (scope : List Nat) : List Nat :=
  scope ++ data.declared.map Prod.fst ++ data.recorded.map Prod.fst ++ data.primitives.map Prod.fst

structure Represented (r : Registry) (ctx : Context) (data : Data) : Prop where
  fromDeclaration : r.constructors = overlay data.fallback data.declared
  fromSnapshot : ctx.state.constructors = overlay data.fallback data.recorded
  fromPrimitives : ctx.interpretation.primitives = overlay (fun _ => none) data.primitives

theorem outside_declared {data : Data} {scope : List Nat} {key : Nat}
    (other : key ∉ data.extended scope) : key ∉ data.declared.map Prod.fst := by
  unfold Data.extended at other
  simp only [List.mem_append,not_or] at other
  exact other.1.1.2

theorem outside_recorded {data : Data} {scope : List Nat} {key : Nat}
    (other : key ∉ data.extended scope) : key ∉ data.recorded.map Prod.fst := by
  unfold Data.extended at other
  simp only [List.mem_append,not_or] at other
  exact other.1.2

theorem outside_primitive {data : Data} {scope : List Nat} {key : Nat}
    (other : key ∉ data.extended scope) : key ∉ data.primitives.map Prod.fst := by
  unfold Data.extended at other
  simp only [List.mem_append,not_or] at other
  exact other.2

theorem completed_residual (r : Registry) (ctx : Context) (data : Data) (scope : List Nat)
    (representation : Represented r ctx data) : OffScope (data.extended scope) r ctx := by
  apply offscope_from_common_default _ _ _ data.fallback
  · intro key outside
    rw [representation.fromDeclaration]
    exact default_outside _ _ _ (outside_declared outside)
  · intro key outside
    rw [representation.fromSnapshot]
    exact default_outside _ _ _ (outside_recorded outside)
  · intro key primitive present
    by_cases covered : key ∈ data.extended scope
    · exact covered
    · rw [representation.fromPrimitives,default_outside _ _ _ (outside_primitive covered)] at present
      cases present

theorem closed_world_iff (r : Registry) (ctx : Context) (data : Data) (scope : List Nat)
    (representation : Represented r ctx data) :
    Metadata r ctx ↔ certify (data.extended scope) r.constructors ctx.interpretation
      ctx.state.constructors ctx.interpretation = .good := by
  rw [metadata_iff]
  exact ⟨And.left,fun accepted => ⟨accepted,completed_residual r ctx data scope representation⟩⟩

end Yulang.GeneralObservedMetadataOverlay290
