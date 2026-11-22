import Yulang.GeneralDeclarativeWhereRawReads346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWherePlain346
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalVersionedExpressionFrame236 (reads readsMany)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeWhereRawExpr346 (compile)
open Core.PresenceGeneration (TyTerm)

inductive Plain : Expr → Prop where
  | name : Plain (.variable n)
  | scalar : Plain (.primitive (.scalar k) [])
  | pair : Plain a → Plain b → Plain (.primitive .pair [a,b])
  | width : Plain (.primitive .emptyRecord [])
  | exactEnd : Plain (.primitive .exactEmpty [])
  | record : Plain a → Plain b → Plain (.record label a b)
  | variant : Plain a → Plain (.variant tag a)
  | join : Plain a → Plain b → Plain (.join a b)

theorem complete {e : Expr} (shape : Plain e) (locate : Nat → Option (Fin n)) (mode : Mode)
    (available : ∀ r ∈ reads mode e, ∃ i, locate r.2 = some i) :
    ∃ term, compile locate e = some term := by
  induction shape with
  | name =>
    obtain ⟨i,was⟩ := available _ List.mem_cons_self
    exact ⟨.var i,by simp [compile,was] <;> rfl⟩
  | scalar | width | exactEnd => exact ⟨_,rfl⟩
  | variant _ ih =>
    obtain ⟨a,was⟩ := ih available
    exact ⟨_,by simp [compile,was] <;> rfl⟩
  | @pair exprA exprB _ _ ih ih' =>
    have first : ∀ r ∈ reads mode exprA, ∃ i, locate r.2 = some i := by
      intro r h
      apply available r
      exact List.mem_append_left _ h
    have last : ∀ r ∈ reads mode exprB, ∃ i, locate r.2 = some i := by
      intro r h
      apply available r
      exact List.mem_append_right _ (List.mem_append_left _ h)
    obtain ⟨a,h⟩ := ih first
    obtain ⟨b,k⟩ := ih' last
    exact ⟨_,by simp [compile,h,k] <;> rfl⟩
  | record _ _ ih ih' | join _ _ ih ih' =>
    obtain ⟨a,h⟩ := ih (fun r h => available r (List.mem_append_left _ h))
    obtain ⟨b,k⟩ := ih' (fun r h => available r (List.mem_append_right _ h))
    exact ⟨_,by simp [compile,h,k] <;> rfl⟩

theorem subset {e : Expr} (locate : Nat → Option (Fin n)) {term : TyTerm (Fin n)}
    (ran : compile locate e = some term) : Plain e := by
  cases e with
  | «variable» name => exact .name
  | primitive constructor args =>
    cases constructor with
    | scalar _ =>
      cases args with
      | nil => exact .scalar
      | cons => cases ran
    | emptyRecord =>
      cases args with
      | nil => exact .width
      | cons => cases ran
    | exactEmpty =>
      cases args with
      | nil => exact .exactEnd
      | cons => cases ran
    | pair =>
      cases args with
      | nil => cases ran
      | cons x xs =>
        cases xs with
        | nil => cases ran
        | cons y rest =>
          cases rest with
          | cons => cases ran
          | nil =>
            cases a : compile locate x <;> cases b : compile locate y <;> simp [compile,a,b] at ran
            exact .pair (subset locate a) (subset locate b)
  | nominal _ _ => cases ran
  | record label x y =>
    cases a : compile locate x <;> cases b : compile locate y <;> simp [compile,a,b] at ran
    exact .record (subset locate a) (subset locate b)
  | variant tag x =>
    cases a : compile locate x <;> simp [compile,a] at ran
    exact .variant (subset locate a)
  | join x y =>
    cases a : compile locate x <;> cases b : compile locate y <;> simp [compile,a,b] at ran
    exact .join (subset locate a) (subset locate b)
termination_by sizeOf e
decreasing_by all_goals subst_vars; simp_wf; omega

theorem exact_domain {e : Expr} (locate : Nat → Option (Fin n)) (mode : Mode) :
    (∃ term, compile locate e = some term) ↔
      Plain e ∧ ∀ r ∈ reads mode e, ∃ i, locate r.2 = some i := by
  constructor
  · rintro ⟨term,ran⟩
    exact ⟨subset locate ran,fun r h => (GeneralDeclarativeWhereRawReads346.located locate mode e ran r h).2⟩
  · rintro ⟨shape,available⟩
    exact complete shape locate mode available

end Yulang.GeneralDeclarativeWherePlain346
