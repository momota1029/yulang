import Yulang.GeneralDeclarativeBounds319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3300000
/-! Logical constructor equations and their syntax-directed head/capture
readback. These names are argument variables, not physical addresses. -/
namespace Yulang.GeneralDeclarativeHead320
open CommonNominalFullCarrier (Ty Subtype Equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr value values translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eval eqv_refl eqv_trans record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra compiled_normalized primitive_congr nominal_congr)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalMatchedAssembly (Aligned)

structure Equation where
  left : Nat
  right : Expr

/-- These are additional ordinary equations in logical names. The right
side has invariant nominal constructors, unlike the core presence atoms. -/
structure State where
  normal : GeneralDeclarativeWhere319.State
  equations : List Equation

def environment (m : Assignment) : GeneralNominalMaterialization.Mode → Nat → Ty :=
  fun _ name => (m name).1

def Models (s : State) (m : Assignment) : Prop :=
  GeneralDeclarativeWhere319.Models s.normal m ∧
  ∀ equation ∈ s.equations, Equivalent (m equation.left).1
    (value (environment m) .actual equation.right)

theorem old_models (normal : GeneralDeclarativeWhere319.State) (m : Assignment) :
    Models ⟨normal,[]⟩ m ↔ GeneralDeclarativeWhere319.Models normal m :=
  ⟨fun h => h.1,fun h => ⟨h,fun _ none => by cases none⟩⟩

def byMode (c : Capture) : Mode → Nat
  | .lower => c.lower
  | .actual => c.center
  | .upper => c.upper

theorem variables_eq (capture : Nat → Capture) (m : Assignment) (mode : Mode) (binder : Nat) :
    variables capture m mode binder = (m (byMode (capture binder) mode)).1 := by
  cases mode <;> rfl

/-- A local constructor is justified by a visible logical equation, and a
capture by mutual ordinary bounds to its one shared center. The rules do not
quantify over models or contain an instance-evidence premise. -/
inductive Read (s : State) (captures : Nat → Capture) : Mode → Nat → Expr → Prop where
  | capture :
      Bound s.normal name (byMode (captures binder) mode) →
      Bound s.normal (byMode (captures binder) mode) name →
      Read s captures mode name (.variable binder)
  | primitive {n : Nat} (source : Fin n → Nat) (child : Fin n → Expr) :
      ⟨name,.primitive ctor (List.ofFn fun i => .variable (source i))⟩ ∈ s.equations →
      (∀ i, Read s captures mode (source i) (child i)) →
      Read s captures mode name (.primitive ctor (List.ofFn child))
  | nominal {n : Nat} (source : Fin n → Nat) (child : Fin n → Expr) :
      ⟨name,.nominal ctor (List.ofFn fun i => .variable (source i))⟩ ∈ s.equations →
      (∀ i, Read s captures .actual (source i) (child i)) →
      Read s captures mode name (.nominal ctor (List.ofFn child))
  | record {l r : Nat} :
      ⟨name,.record label (.variable l) (.variable r)⟩ ∈ s.equations →
      Read s captures mode l p → Read s captures mode r q →
      Read s captures mode name (.record label p q)
  | variant {child : Nat} :
      ⟨name,.variant tag (.variable child)⟩ ∈ s.equations →
      Read s captures mode child part →
      Read s captures mode name (.variant tag part)
  | join {l r : Nat} :
      ⟨name,.join (.variable l) (.variable r)⟩ ∈ s.equations →
      Read s captures mode l p → Read s captures mode r q →
      Read s captures mode name (.join p q)

theorem values_ofFn {n : Nat} (f : Fin n → Expr) (env) (mode) :
    values env mode (List.ofFn f) = List.ofFn (fun i => value env mode (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,values,ih]

theorem aligned_ofFn {n : Nat} (l r : Fin n → Ty)
    (facts : ∀ i, Equivalent (l i) (r i)) :
    Aligned Equivalent (List.ofFn l) (List.ofFn r) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (facts 0) (ih _ _ (fun i => facts i.succ))

theorem read_sound {s : State} {captures : Nat → Capture} {name : Nat} {e : Expr}
    {mode : Mode} (proof : Read s captures mode name e) (m : Assignment) (valid : Models s m) :
    Equivalent (m name).1 (value (variables captures m) mode e) := by
  induction proof with
  | capture one two =>
    rw [value,variables_eq]
    exact ⟨bound_sound m valid.1 one,bound_sound m valid.1 two⟩
  | primitive source child read parts ih =>
    apply eqv_trans (valid.2 _ read)
    simp only [value,values_ofFn]
    exact primitive_congr _ (aligned_ofFn _ _ ih)
  | nominal source child read parts ih =>
    apply eqv_trans (valid.2 _ read)
    simp only [value,values_ofFn]
    exact nominal_congr _ (aligned_ofFn _ _ ih)
  | record read _ _ left right =>
    exact eqv_trans (valid.2 _ read) (record_congr _ left right)
  | variant read _ inner =>
    exact eqv_trans (valid.2 _ read) (variant_congr _ inner)
  | join read _ _ left right =>
    exact eqv_trans (valid.2 _ read) (union_congr left right)

theorem source_head {s : State} {capture : Nat → Capture} {name : Nat}
    {catalogue : Constructors} {interp} {pattern : Pattern} {e : Expr}
    (compiled : translate catalogue interp pattern = some e)
    (derived : Read s capture .actual name e) (m : Assignment) (valid : Models s m) :
    Equivalent (m name).1 (eval (algebra catalogue interp) (variables capture m .actual)
      (normalize pattern)) :=
  eqv_trans (read_sound derived m valid) (compiled_normalized compiled)

end Yulang.GeneralDeclarativeHead320
