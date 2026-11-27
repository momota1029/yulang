import Yulang.GeneralDeclarativeI65I74WhereForest450

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Derivation
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation State)
open WhereSites450 (alias_wire_from_actual_derivation450)
local notation "Raw" => GeneralDeclarativeHead320.State
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralDeclarativeCongruence322 (Congruent Arguments)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeWitnessEquation349 (Code Checked CheckedArgs)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)

mutual
inductive EqWire where
  | old (w : Code)
  | alias (first last : Nat) (w : Link)
  | reverse (w : EqWire)
  | compose (first last : EqWire)
  | primitive (head : Primitive) (args : ArgWire)
  | nominal (head : Nat) (args : ArgWire)
  | pairFirst (w : EqWire)
  | pairSecond (w : EqWire)
  | record (head : Nat) (field rest : EqWire)
  | variant (head : Nat) (field : EqWire)
  | union (first last : EqWire)
inductive ArgWire where
  | nil
  | cons (head : EqWire) (rest : ArgWire)
end

def dropPair {s : Raw} (p : Checked s) (first : Bool) : Option (Checked s) :=
  match left : p.left, right : p.right with
  | .primitive .pair [a,x], .primitive .pair [b,y] =>
    have both : Derives s (.primitive .pair [a,x]) (.primitive .pair [b,y]) :=
      left ▸ right ▸ p.derivation
    if first then some ⟨a,b,.pairFirst both⟩ else some ⟨x,y,.pairSecond both⟩
  | _,_ => none

mutual
def readEq (s : Raw) : EqWire → Option (Checked s)
  | .old w => GeneralDeclarativeWitnessEquation349.replay s w
  | .alias a b w =>
    if ok : checksLink s a b w = true then
      some ⟨.variable a,.variable b,.congruent (.variable (link ok))⟩
    else none
  | .reverse w => (readEq s w).map fun x => ⟨x.right,x.left,.symm x.derivation⟩
  | .compose l r => do
    let x ← readEq s l
    let y ← readEq s r
    if ok : eqExpr x.right y.left = true then
      let mid := (eq_expr _ _).mp ok
      some ⟨x.left,y.right,.trans x.derivation (mid.symm ▸ y.derivation)⟩
    else none
  | .primitive k args => do
    let q ← readArgs s args
    pure ⟨.primitive k q.left,.primitive k q.right,.primitive q.derivation⟩
  | .nominal k args => do
    let q ← readArgs s args
    pure ⟨.nominal k q.left,.nominal k q.right,.nominal q.derivation⟩
  | .pairFirst w => (readEq s w).bind fun x => dropPair x true
  | .pairSecond w => (readEq s w).bind fun x => dropPair x false
  | .record k left right => do
    let x ← readEq s left
    let y ← readEq s right
    pure ⟨.record k x.left y.left,.record k x.right y.right,.record x.derivation y.derivation⟩
  | .variant k w => (readEq s w).map fun x => ⟨.variant k x.left,.variant k x.right,.variant x.derivation⟩
  | .union l r => do
    let x ← readEq s l
    let y ← readEq s r
    pure ⟨.join x.left y.left,.join x.right y.right,.join x.derivation y.derivation⟩
termination_by w => sizeOf w

def readArgs (s : Raw) : ArgWire → Option (CheckedArgs s)
  | .nil => some ⟨[],[],.nil⟩
  | .cons head tail => do
    let x ← readEq s head
    let y ← readArgs s tail
    pure ⟨x.left::y.left,x.right::y.right,.cons x.derivation y.derivation⟩
termination_by w => sizeOf w
end

private theorem old_congruence_has_wire453 {s : Raw} {a b : Expr} (h : Congruent s a b) :
    ∃ wire, readEq s wire = some ⟨a,b,.congruent h⟩ := by
  induction h using Congruent.rec (motive_2 := fun lhs rhs _ =>
    ∃ w, ∃ d : Forest s lhs rhs, readArgs s w = some ⟨lhs,rhs,d⟩)
  case «variable» a b proof =>
    obtain ⟨w,ok⟩ := alias_wire_from_actual_derivation450 proof
    exact ⟨.alias a b w,by simp [readEq,ok]⟩
  case primitive _ _ tag _ ih =>
    obtain ⟨w,d,ok⟩ := ih
    exact ⟨.primitive tag w,by simp [readEq,ok,Bind.bind,Option.bind]⟩
  case nominal _ _ tag _ ih =>
    obtain ⟨w,d,ok⟩ := ih
    exact ⟨.nominal tag w,by simp [readEq,ok,Bind.bind,Option.bind]⟩
  case record _ _ _ _ label _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    exact ⟨.record label x y,by simp [readEq,hx,hy,Bind.bind,Option.bind]⟩
  case variant _ _ label _ ih =>
    obtain ⟨x,hx⟩ := ih
    exact ⟨.variant label x,by simp [readEq,hx]⟩
  case join _ _ _ _ _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    exact ⟨.union x y,by simp [readEq,hx,hy,Bind.bind,Option.bind]⟩
  case nil => exact ⟨.nil,.nil,by simp [readArgs]⟩
  case cons _ _ _ _ headProof _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,d,hy⟩ := right
    exact ⟨.cons x y,.cons (.congruent headProof) d,by simp [readArgs,hx,hy,Bind.bind,Option.bind]⟩

theorem every_independent_finite_Derives_has_data_wire453 {s : Raw} {a b : Expr}
    (h : Derives s a b) : ∃ w, readEq s w = some ⟨a,b,h⟩ := by
  induction h using Derives.rec (motive_2 := fun lhs rhs d =>
    ∃ w, readArgs s w = some ⟨lhs,rhs,d⟩)
  case row name exp row =>
    obtain ⟨i,atI⟩ := List.mem_iff_getElem?.mp row
    refine ⟨.old (.currentRow i),?_⟩
    simp only [readEq,GeneralDeclarativeWitnessEquation349.replay]
    split
    · rename_i missing
      rw [atI] at missing
      contradiction
    · rename_i e found
      cases Option.some.inj (found.symm.trans atI)
      rfl
  case congruent _ _ h => exact old_congruence_has_wire453 h
  case refl e => exact ⟨.old (.refl e),by simp [readEq,GeneralDeclarativeWitnessEquation349.replay]⟩
  case symm _ _ _ before =>
    obtain ⟨w,read⟩ := before
    exact ⟨.reverse w,by simp [readEq,read]⟩
  case trans _ mid _ _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    have eq := (eq_expr mid mid).mpr rfl
    exact ⟨.compose x y,by simp [readEq,hx,hy,eq,Bind.bind,Option.bind]⟩
  case primitive _ _ tag _ ih =>
    obtain ⟨w,ok⟩ := ih
    exact ⟨.primitive tag w,by simp [readEq,ok,Bind.bind,Option.bind]⟩
  case nominal _ _ tag _ ih =>
    obtain ⟨w,ok⟩ := ih
    exact ⟨.nominal tag w,by simp [readEq,ok,Bind.bind,Option.bind]⟩
  case pairFirst _ _ _ _ _ ih =>
    obtain ⟨w,ok⟩ := ih
    exact ⟨.pairFirst w,by simp [readEq,ok,dropPair]⟩
  case pairSecond _ _ _ _ _ ih =>
    obtain ⟨w,ok⟩ := ih
    exact ⟨.pairSecond w,by simp [readEq,ok,dropPair]⟩
  case record _ _ _ _ label _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    exact ⟨.record label x y,by simp [readEq,hx,hy,Bind.bind,Option.bind]⟩
  case variant _ _ label _ ih =>
    obtain ⟨x,hx⟩ := ih
    exact ⟨.variant label x,by simp [readEq,hx]⟩
  case join _ _ _ _ _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    exact ⟨.union x y,by simp [readEq,hx,hy,Bind.bind,Option.bind]⟩
  case nil => exact ⟨.nil,by simp [readArgs]⟩
  case cons _ _ _ _ _ _ left right =>
    obtain ⟨x,hx⟩ := left
    obtain ⟨y,hy⟩ := right
    exact ⟨.cons x y,by simp [readArgs,hx,hy,Bind.bind,Option.bind]⟩

def checkEq (s : Raw) (a b : Expr) (w : EqWire) : Bool :=
  ((readEq s w).map fun q => eqExpr q.left a && eqExpr q.right b).getD false

theorem exact_finite_data_eq_check_iff_independent_Derives453 (s : Raw) (a b : Expr) :
    (∃ wire, checkEq s a b wire = true) ↔ Derives s a b := by
  constructor
  · rintro ⟨w,checked⟩
    cases h : readEq s w with
    | none => simp [checkEq,h] at checked
    | some q =>
      have exact : q.left = a ∧ q.right = b := by
        simpa [checkEq,h,Bool.and_eq_true,eq_expr] using checked
      exact exact.1 ▸ exact.2 ▸ q.derivation
  · intro h
    obtain ⟨w,found⟩ := every_independent_finite_Derives_has_data_wire453 h
    exact ⟨w,by simp [checkEq,found,(eq_expr a a).mpr rfl,(eq_expr b b).mpr rfl]⟩




end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.Derivation
