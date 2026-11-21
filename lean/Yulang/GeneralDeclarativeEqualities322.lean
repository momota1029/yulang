import Yulang.GeneralDeclarativeCongruence322
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEqualities322
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeCongruence322 (Congruent)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Equivalent common_pair_iff)

mutual
/-- Ordinary constructor congruence and substitution of recorded equations
under constructors. This proof reads source equality facts, not evidence
for any role. It intentionally makes no completeness claim. -/
inductive Derives (s : State) : Expr → Expr → Prop where
  | row : (⟨name,exp⟩ : Equation) ∈ s.equations → Derives s (.variable name) exp
  | congruent : Congruent s a b → Derives s a b
  | refl (exp : Expr) : Derives s exp exp
  | symm : Derives s a b → Derives s b a
  | trans : Derives s a b → Derives s b c → Derives s a c
  | primitive : Forest s as bs → Derives s (.primitive tag as) (.primitive tag bs)
  | nominal : Forest s as bs → Derives s (.nominal tag as) (.nominal tag bs)
  | pairFirst : Derives s (.primitive .pair [a,p]) (.primitive .pair [b,q]) → Derives s a b
  | pairSecond : Derives s (.primitive .pair [a,p]) (.primitive .pair [b,q]) → Derives s p q
  | record : Derives s a b → Derives s x y → Derives s (.record label a x) (.record label b y)
  | variant : Derives s a b → Derives s (.variant label a) (.variant label b)
  | join : Derives s a b → Derives s x y → Derives s (.join a x) (.join b y)
inductive Forest (s : State) : List Expr → List Expr → Prop where
  | nil : Forest s [] []
  | cons : Derives s a b → Forest s as bs → Forest s (a :: as) (b :: bs)
end

theorem semantic {s : State} (proof : Derives s a b) (m : Assignment) (valid : Models s m) :
    Equivalent (value (environment m) .actual a) (value (environment m) .actual b) :=
  Derives.rec
    (motive_1 := fun a b _ => Equivalent (value (environment m) .actual a) (value (environment m) .actual b))
    (motive_2 := fun as bs _ => Aligned Equivalent (values (environment m) .actual as) (values (environment m) .actual bs))
    (fun h => valid.2 _ h)
    (fun h => GeneralDeclarativeCongruence322.sound h m valid .actual)
    (fun _ => eqv_refl _)
    (fun _ ih => eqv_symm ih)
    (fun _ _ ih jh => eqv_trans ih jh)
    (fun _ ih => primitive_congr _ ih)
    (fun _ ih => nominal_congr _ ih)
    (fun _ ih =>
      ⟨((common_pair_iff ..).mp ih.1).1,((common_pair_iff ..).mp ih.2).1⟩)
    (fun _ ih =>
      ⟨((common_pair_iff ..).mp ih.1).2,((common_pair_iff ..).mp ih.2).2⟩)
    (fun _ _ ih jh => record_congr _ ih jh)
    (fun _ ih => variant_congr _ ih)
    (fun _ _ ih jh => union_congr ih jh)
    .nil
    (fun _ _ ih jh => .cons ih jh)
    proof

theorem entails {s : State} (proof : Derives s (.variable name) exp) :
    Entails s ⟨name,exp⟩ :=
  fun m valid => semantic proof m valid

theorem by_stored_alias {s : State} (stored : (⟨owner,raw⟩ : Equation) ∈ s.equations)
    (source : Alias s name owner) (inside : Congruent s raw exposed) :
    Derives s (.variable name) exposed :=
  .trans (.congruent (.variable source)) (.trans (.row stored) (.congruent inside))

end Yulang.GeneralDeclarativeEqualities322
