import Yulang.GeneralDeclarativeTermOccurrences322
import Yulang.GeneralDeclarativeInequality322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedActual323
open GeneralDeclarativeHead320 (State Models environment byMode)
open GeneralDeclarativeSubstitution320 (logical logicals)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans eqv_refl)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Ty Equivalent common_pair_iff nominal nominal_regular_invariant_exact)
open GeneralNominalCommonBridge (Assignment)

def eqAt (m : Assignment) (a b : Expr) : Prop :=
  Equivalent (value (environment m) .actual a) (value (environment m) .actual b)

def OccursAt (m : Assignment) (cap : Nat → Capture) (o : Occurrence) : Prop :=
  eqAt m o.term (.variable (byMode (cap o.binder) o.mode))

mutual
/-- Independent actual observations for the constructor positions in
which equality is cancellative in this carrier. This fragment does not
reverse through joins, shadowed fields, or non-injective constructors. -/
inductive Rigid : Mode → Expr → Expr → List Occurrence → Prop where
  | capture : Rigid mode term (.variable binder) [⟨binder,mode,term⟩]
  | pair : Rigid mode a x first → Rigid mode b y second →
      Rigid mode (.primitive .pair [a,b]) (.primitive .pair [x,y]) (first ++ second)
  | nominal : RigidMany .actual xs ys seen → Rigid mode (.nominal tag xs) (.nominal tag ys) seen
  | scalar : Rigid mode (.primitive (.scalar b) []) (.primitive (.scalar b) []) []
inductive RigidMany : Mode → List Expr → List Expr → List Occurrence → Prop where
  | nil : RigidMany mode [] [] []
  | cons : Rigid mode a b first → RigidMany mode as bs second →
      RigidMany mode (a :: as) (b :: bs) (first ++ second)
end

def BindsAt (m : Assignment) (cap : Nat → Capture) (seen : List Occurrence) : Prop :=
  ∀ o ∈ seen, OccursAt m cap o

theorem split_binds (m : Assignment) (cap : Nat → Capture) (before after : List Occurrence) :
    BindsAt m cap (before ++ after) ↔ BindsAt m cap before ∧ BindsAt m cap after := by
  constructor
  · intro all
    exact ⟨fun o h => all o (List.mem_append_left _ h),fun o h => all o (List.mem_append_right _ h)⟩
  · rintro ⟨a,b⟩ o found
    exact (List.mem_append.mp found).elim (a o) (b o)

theorem pair_exact (a b c d : Ty) :
    Equivalent (CommonNominalFullCarrier.pair a b) (CommonNominalFullCarrier.pair c d) ↔
    Equivalent a c ∧ Equivalent b d := by
  constructor
  · rintro ⟨first,last⟩
    obtain ⟨ac,bd⟩ := (common_pair_iff ..).mp first
    obtain ⟨ca,db⟩ := (common_pair_iff ..).mp last
    exact ⟨⟨ac,ca⟩,⟨bd,db⟩⟩
  · rintro ⟨ac,bd⟩
    exact ⟨(common_pair_iff ..).mpr ⟨ac.1,bd.1⟩,(common_pair_iff ..).mpr ⟨ac.2,bd.2⟩⟩


theorem aligned_exact {xs ys : List Ty}
    (lengths : xs.length = ys.length)
    (positions : ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → Equivalent x y) :
    Aligned Equivalent xs ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .nil
    | cons => cases lengths
  | cons x rest ih =>
    cases ys with
    | nil => cases lengths
    | cons y tail =>
      exact .cons (positions 0 x y rfl rfl)
        (ih (Nat.succ.inj lengths) (fun i a b hx hy => positions (i+1) a b hx hy))

theorem nominal_exact (tag : Nat) (xs ys : List Ty) :
    Equivalent (nominal tag (xs.map Sum.inl)) (nominal tag (ys.map Sum.inl)) ↔
    Aligned Equivalent xs ys := by
  constructor
  · intro equal
    obtain ⟨_,arity,pointwise⟩ := (nominal_regular_invariant_exact ..).mp equal.1
    apply aligned_exact (by simpa using arity)
    intro i x y hx hy
    exact pointwise i (.inl x) (.inl y)
      (by simp [List.getElem?_map,hx]) (by simp [List.getElem?_map,hy])
  · exact nominal_congr tag

/-- Concrete actual observations are an *exact* rather than just
sufficient condition on the visited shared values for these heads. -/
theorem rigid_exact (m : Assignment) (cap : Nat → Capture)
    (read : Rigid mode term code seen) :
    eqAt m term (logical cap mode code) ↔ BindsAt m cap seen := by
  let here := environment m
  induction read using Rigid.rec
    (motive_2 := fun mode ts cs seen _ =>
      Aligned Equivalent (values here .actual ts) (values here .actual (logicals cap mode cs)) ↔
        BindsAt m cap seen) with
  | capture =>
    simp [BindsAt,OccursAt,logical]
  | pair first next ih jh =>
    exact (pair_exact ..).trans ((and_congr ih jh).trans (split_binds ..).symm)
  | nominal steps ih =>
    exact (nominal_exact ..).trans ih
  | scalar =>
    exact ⟨fun _ o nowhere => False.elim (List.not_mem_nil nowhere),fun _ => eqv_refl _⟩
  | nil =>
    exact ⟨fun _ o nowhere => False.elim (List.not_mem_nil nowhere),fun _ => .nil⟩
  | cons first next ih jh =>
    constructor
    · intro both
      cases both with
      | cons h t => exact (split_binds ..).mpr ⟨ih.mp h,jh.mp t⟩
    · intro both
      obtain ⟨h,t⟩ := (split_binds ..).mp both
      exact .cons (ih.mpr h) (jh.mpr t)

end Yulang.GeneralDeclarativeRepeatedActual323
