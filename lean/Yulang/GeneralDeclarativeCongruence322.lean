import Yulang.GeneralDeclarativeAliasMeaning321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCongruence322
open GeneralDeclarativeHead320 (State Models environment)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Equivalent)

/-! A fixed logical formula may read already-existing names behind aliases.
This is a syntactic derivation; it does not search for a fitting model. -/
mutual
  inductive Congruent (s : State) : Expr → Expr → Prop where
  | variable : Alias s a b → Congruent s (.variable a) (.variable b)
  | primitive : Arguments s xs ys → Congruent s (.primitive tag xs) (.primitive tag ys)
  | nominal : Arguments s xs ys → Congruent s (.nominal tag xs) (.nominal tag ys)
  | record : Congruent s a b → Congruent s p q →
      Congruent s (.record label a p) (.record label b q)
  | variant : Congruent s a b → Congruent s (.variant label a) (.variant label b)
  | join : Congruent s a b → Congruent s p q →
      Congruent s (.join a p) (.join b q)
  inductive Arguments (s : State) : List Expr → List Expr → Prop where
  | nil : Arguments s [] []
  | cons : Congruent s a b → Arguments s as bs → Arguments s (a :: as) (b :: bs)
end

theorem sound {s : State} (derivation : Congruent s a b) (m : Assignment) (valid : Models s m) :
    ∀ mode : Mode, Equivalent (value (environment m) mode a) (value (environment m) mode b) :=
  Congruent.rec
    (motive_1 := fun a b _ => ∀ mode, Equivalent (value (environment m) mode a) (value (environment m) mode b))
    (motive_2 := fun a b _ => ∀ mode, Aligned Equivalent (values (environment m) mode a) (values (environment m) mode b))
    (fun h _ => alias_sound h m valid)
    (fun _ ih mode => primitive_congr _ (ih mode))
    (fun _ ih _ => nominal_congr _ (ih .actual))
    (fun _ _ ih jh mode => record_congr _ (ih mode) (jh mode))
    (fun _ ih mode => variant_congr _ (ih mode))
    (fun _ _ ih jh mode => union_congr (ih mode) (jh mode))
    (fun _ => .nil)
    (fun _ _ ih jh mode => .cons (ih mode) (jh mode))
    derivation

end Yulang.GeneralDeclarativeCongruence322
