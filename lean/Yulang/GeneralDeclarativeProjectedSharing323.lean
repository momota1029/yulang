import Yulang.GeneralDeclarativeActualPoint323
import Yulang.GeneralDeclarativeExactWalk323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectedSharing323
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeInequality322 (Le sound)
open GeneralDeclarativeSemanticSharing323 (SameBinder)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent common_pair_iff common_variant_iff nominal_regular_invariant_exact)

/-- Paths carry only consulted constructor positions. A one-way ordinary
bound becomes two-way at an invariant nominal argument, and stays two-way
when following ordinary covariant pair positions or exact single tags. -/
inductive Step : Expr → Expr → Expr → Expr → Bool → Prop where
  | left : Step (.primitive .pair [a,c]) (.primitive .pair [b,d]) a b false
  | right : Step (.primitive .pair [a,c]) (.primitive .pair [b,d]) c d false
  | tagged : Step (.variant tag a) (.variant tag b) a b false
  | invariant (i : Nat) : xs[i]? = some a → ys[i]? = some b →
      Step (.nominal k xs) (.nominal k ys) a b true

inductive Path : Expr → Expr → Expr → Expr → Bool → Prop where
  | here : Path a b a b false
  | next : Step a b x y here → Path x y u v later → Path a b u v (here || later)

def subAt (m : Assignment) (a b : Expr) : Prop :=
  Subtype (value (environment m) .actual a) (value (environment m) .actual b)

structure Compared (m : Assignment) (isInvariant : Bool) (a b : Expr) : Prop where
  goes : subAt m a b
  returns : isInvariant = true → subAt m b a

theorem nominal_payload (m : Assignment) {i : Nat} (hasL : xs[i]? = some a) (hasR : ys[i]? = some b)
    (order : subAt m (.nominal tag xs) (.nominal tag ys)) : eqAt m a b := by
  have relation := (nominal_regular_invariant_exact ..).mp order
  have mapped (args : List Expr) :
      values (environment m) .actual args = args.map (value (environment m) .actual) := by
    induction args with
    | nil => rfl
    | cons first rest ih => simp [values,ih]
  exact relation.2.2 i (.inl (value (environment m) .actual a))
    (.inl (value (environment m) .actual b))
    (by simp [mapped,List.getElem?_map,hasL])
    (by simp [mapped,List.getElem?_map,hasR])

theorem step_forward (chosen : Step a b x y locked) (order : subAt m a b) : Compared m locked x y := by
  cases chosen with
  | left => exact ⟨((common_pair_iff ..).mp order).1,fun bad => by cases bad⟩
  | right => exact ⟨((common_pair_iff ..).mp order).2,fun bad => by cases bad⟩
  | tagged => exact ⟨(common_variant_iff ..).mp order,fun bad => by cases bad⟩
  | invariant _ l r =>
    have got := nominal_payload m l r order
    exact ⟨got.1,fun _ => got.2⟩

theorem reverse (chosen : Step a b x y locked) : Step b a y x locked := by
  cases chosen with
  | left => exact .left
  | right => exact .right
  | tagged => exact .tagged
  | invariant i a b => exact .invariant i b a

theorem path_backward (chosen : Path lhs rhs x y locks) (order : subAt m rhs lhs) :
    subAt m y x := by
  induction chosen with
  | here => exact order
  | next step rest ih => exact ih (step_forward (reverse step) order).goes

theorem path_forward (chosen : Path lhs rhs x y locks) (order : subAt m lhs rhs) :
    Compared m locks x y := by
  induction chosen with
  | here => exact ⟨order,fun bad => by cases bad⟩
  | next step rest ih =>
    have first := step_forward step order
    have continued := ih first.goes
    refine ⟨continued.goes,?_⟩
    intro locked
    simp only [Bool.or_eq_true] at locked
    rcases locked with early|late
    · exact path_backward rest (first.returns early)
    · exact continued.returns late

open GeneralDeclarativeTermWalk322 (Occurrence)

/-- Actual sharing can be supplied by an ordinary projected source bound:
every repeated pair is compared at a path that goes through an invariant
parameter somewhere. No requirement that the underlying logical names
be syntactically equal. -/
theorem share {s : State} {seen : List Occurrence}
    (origins : ∀ x ∈ seen, ∀ y ∈ seen, x.binder = y.binder →
      ∃ lhs rhs, Le s lhs rhs ∧ Path lhs rhs x.term y.term true) :
    SameBinder s seen := by
  intro x hx y hy same m valid
  obtain ⟨lhs,rhs,known,path⟩ := origins x hx y hy same
  have all := path_forward path (sound known m valid)
  exact ⟨all.goes,all.returns rfl⟩

end Yulang.GeneralDeclarativeProjectedSharing323
