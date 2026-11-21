import Yulang.GeneralDeclarativeRigidOccurrences323
import Yulang.GeneralNominalStructuralReadback

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactWalk323
open GeneralDeclarativeHead320 (environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical logicals)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeRigidOccurrences323 (as_walk)
open GeneralDeclarativeRepeatedActual323 (Rigid eqAt BindsAt rigid_exact pair_exact nominal_exact split_binds)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl record_congr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier (Ty Equivalent variant common_variant_iff)

/-- A constructor readback explanation with exact projected obligations.
The walk remains syntactic; the semantic property never names a choice
of impl, emitted child, or output equation. -/
structure Exact (mode : Mode) (term code : Expr) (seen : List Occurrence) : Prop where
  walked : Walk mode term code seen
  semantic : ∀ m cap, eqAt m term (logical cap mode code) ↔ BindsAt m cap seen

theorem of_rigid (read : Rigid mode term code seen) : Exact mode term code seen :=
  ⟨as_walk read,fun m cap => rigid_exact m cap read⟩

theorem variant_exact (tag : Nat) (x y : Ty) :
    Equivalent (variant tag x) (variant tag y) ↔ Equivalent x y :=
  and_congr (common_variant_iff tag x y) (common_variant_iff tag y x)

theorem tagged (tag : Nat) (body : Exact mode source code seen) :
    Exact mode (.variant tag source) (.variant tag code) seen :=
  ⟨.variant body.walked,fun m cap => (variant_exact ..).trans (body.semantic m cap)⟩

theorem paired (first : Exact mode a p one) (last : Exact mode b q two) :
    Exact mode (.primitive .pair [a,b]) (.primitive .pair [p,q]) (one++two) :=
  ⟨.primitive (.cons first.walked (by simpa using WalkMany.cons last.walked WalkMany.nil)),
    fun m cap => (pair_exact ..).trans
      ((and_congr (first.semantic m cap) (last.semantic m cap)).trans (split_binds ..).symm)⟩

inductive Many (mode : Mode) : List Expr → List Expr → List Occurrence → Prop where
  | nil : Many mode [] [] []
  | cons : Exact mode a b first → Many mode as bs second → Many mode (a::as) (b::bs) (first++second)

theorem many_walk (read : Many mode actual code seen) : WalkMany mode actual code seen := by
  induction read with
  | nil => exact .nil
  | cons head _ ih => exact .cons head.walked ih

theorem args_semantic (read : Many mode actual code seen) (m cap) :
    Aligned Equivalent (values (environment m) .actual actual)
      (values (environment m) .actual (logicals cap mode code)) ↔ BindsAt m cap seen := by
  induction read with
  | nil =>
    exact ⟨fun _ o nowhere => False.elim (List.not_mem_nil nowhere),fun _ => .nil⟩
  | cons head _ ih =>
    constructor
    · intro all
      cases all with
      | cons h t => exact (split_binds ..).mpr ⟨(head.semantic m cap).mp h,ih.mp t⟩
    · intro all
      obtain ⟨h,t⟩ := (split_binds ..).mp all
      exact .cons ((head.semantic m cap).mpr h) (ih.mpr t)

theorem nominal (id : Nat) (read : Many .actual actual code seen) :
    Exact mode (.nominal id actual) (.nominal id code) seen :=
  ⟨.nominal (many_walk read),fun m cap => (nominal_exact ..).trans (args_semantic read m cap)⟩

end Yulang.GeneralDeclarativeExactWalk323
