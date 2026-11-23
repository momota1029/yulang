import Yulang.GeneralDeclarativeWitnessNativeOrder362

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessUnaryVarianceLaws362
open GeneralDeclarativeWitnessFullIntervals357
  (ContextDerives context_derives_nominal_exact context_derives_ordinary_exact rowPart)
open CommonRecursiveNominalIntervals
  (Endpoint Argument Bounds ContextArgumentsRel ArgumentRel effectiveParameter childContext effective_true_used)
open CommonDeclaredNominalInspection (Registry Parameter)
open CommonDeclaredNominalVariance (Variance)
open CommonNominalFullCarrier (Subtype)
open GeneralNominalCommonBridge (Assignment)

def plain (x : Nat) : Endpoint Nat := .ordinary (.var x)
def point (key x : Nat) : Endpoint Nat := .nominal key [.inl (.point (plain x))]
def window (key a b : Nat) : Endpoint Nat := .nominal key [.inl (.interval (plain a) (plain b))]
def wrapped (key : Nat) (inner : Endpoint Nat) : Endpoint Nat := .nominal key [.inl (.point inner)]

theorem known_same_name {table : Registry} {m : Assignment} {c key ps}
    (known : table[key]? = some ps) (args other : List (Argument Nat)) :
    ContextDerives table m c (.nominal key args) (.nominal key other) ↔
      ContextArgumentsRel (ContextDerives table m) (rowPart m) c ps args other := by
  rw [context_derives_nominal_exact]
  simp [known]

theorem ambient_covariant_points {table : Registry} {key a b} (m : Assignment)
    (known : table[key]? = some [⟨.value,.covariant⟩]) :
    ContextDerives table m false (point key a) (point key b) ↔ Subtype (m a).1 (m b).1 := by
  unfold point
  rw [known_same_name known]
  simp [ContextArgumentsRel,ArgumentRel,childContext,plain,context_derives_ordinary_exact]
  rfl

theorem ambient_contravariant_points {table : Registry} {key a b} (m : Assignment)
    (known : table[key]? = some [⟨.value,.contravariant⟩]) :
    ContextDerives table m false (point key a) (point key b) ↔ Subtype (m b).1 (m a).1 := by
  unfold point
  rw [known_same_name known]
  simp [ContextArgumentsRel,ArgumentRel,childContext,plain,context_derives_ordinary_exact]
  rfl

def Compatible (m : Assignment) (a b x y : Nat) : Prop :=
  Subtype (m a).1 (m b).1 ∧ Subtype (m x).1 (m y).1 ∧
  Subtype (m a).1 (m y).1 ∧ Subtype (m x).1 (m b).1

theorem inherited_windows_exact {table : Registry} {key a b x y} (m : Assignment) (variance : Variance)
    (known : table[key]? = some [⟨.value,variance⟩]) (used : variance ≠ .unused) :
    ContextDerives table m true (window key a b) (window key x y) ↔ Compatible m a b x y := by
  unfold window Compatible
  rw [known_same_name known]
  have fixed := effective_true_used (⟨.value,variance⟩ : Parameter) used
  simp [ContextArgumentsRel,ArgumentRel,childContext,fixed,plain,context_derives_ordinary_exact,
    Bounds.lower,Bounds.upper]
  rfl

theorem compatible_symm {m a b x y} (h : Compatible m a b x y) : Compatible m x y a b :=
  ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

/-- The wrapper carries invariant context into the used descendant even
when its source-declared variance is co- or contravariant. With interval
arguments the exact condition is compatibility, not endpoint equality. -/
theorem invariant_parent_reduces_to_compatibility {table : Registry} {outer inner a b x y}
    (m : Assignment) (variance : Variance)
    (outside : table[outer]? = some [⟨.value,.invariant⟩])
    (inside : table[inner]? = some [⟨.value,variance⟩]) (used : variance ≠ .unused) :
    ContextDerives table m false (wrapped outer (window inner a b)) (wrapped outer (window inner x y)) ↔
      Compatible m a b x y := by
  unfold wrapped
  rw [known_same_name outside]
  simp only [ContextArgumentsRel,CommonRecursiveNominalIntervals.effective_false,ArgumentRel,
    childContext,decide_true, Bool.false_or, Bounds.lower,Bounds.upper,and_true]
  rw [inherited_windows_exact m variance inside used,
    inherited_windows_exact m variance inside used,
    inherited_windows_exact m variance inside used,
    inherited_windows_exact m variance inside used]
  constructor
  · exact fun h => h.2.2.1
  · intro h
    exact ⟨⟨h.1,h.1,h.1,h.1⟩,⟨h.2.1,h.2.1,h.2.1,h.2.1⟩,h,compatible_symm h⟩

end Yulang.GeneralDeclarativeWitnessUnaryVarianceLaws362
