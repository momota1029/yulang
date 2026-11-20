import Yulang.GeneralNominalEffectSupport249

/-! Type and row reads are separate components. A row-only dependency can
occur below a compiled nominal or primitive expression. -/
namespace Yulang.GeneralRebaseFiniteRowReads285
open Core.PresenceGeneration
open GeneralPresenceSubstitutionSupport244 (rowSources)
open GeneralPresenceUsedSupport245 (typedReads rowReads)

theorem local_row_eval (model : Model) (a b : Name → Comp model) (term : RowTerm Name)
    (rows : ∀ n ∈ rowSources term, (a n).2 = (b n).2) :
    term.eval model a = term.eval model b := by
  induction term with
  | var n => exact rows n (List.mem_singleton_self _)
  | empty => rfl
  | join l r ih jh =>
    simp only [RowTerm.eval,ih (fun n h => rows n (List.mem_append_left _ h)),
      jh (fun n h => rows n (List.mem_append_right _ h))]

theorem local_type_eval (model : Model) (a b : Name → Comp model) (term : TyTerm Name)
    (types : ∀ n ∈ typedReads term, (a n).1 = (b n).1)
    (rows : ∀ n ∈ rowReads term, (a n).2 = (b n).2) :
    term.eval model a = term.eval model b := by
  induction term with
  | var n => exact types n (List.mem_singleton_self _)
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | union l r ih jh | inter l r ih jh | pair l r ih jh | record _ l r ih jh | recordDefault _ l r ih jh =>
    simp only [TyTerm.eval,ih (fun n h => types n (List.mem_append_left _ h))
      (fun n h => rows n (List.mem_append_left _ h)),
      jh (fun n h => types n (List.mem_append_right _ h))
      (fun n h => rows n (List.mem_append_right _ h))]
  | required l e ih | variant l e ih => simp only [TyTerm.eval,ih types rows]
  | arrow t incoming u outgoing ih jh =>
    have rowt (n) (h : n ∈ rowReads t) := rows n (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
    have rowu (n) (h : n ∈ rowReads u) := rows n (List.mem_append_left _ (List.mem_append_right _ h))
    have rowin (n) (h : n ∈ rowSources incoming) := rows n (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
    have rowout (n) (h : n ∈ rowSources outgoing) := rows n (List.mem_append_right _ h)
    simp only [TyTerm.eval,ih (fun n h => types n (List.mem_append_left _ h)) rowt,
      jh (fun n h => types n (List.mem_append_right _ h)) rowu,
      local_row_eval model a b incoming rowin,local_row_eval model a b outgoing rowout]

open GeneralNominalRebaseEffectView243 (Expr Equation eval evals)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalEffectSupport249 (support supports equationReads)
open CommonNominalFullCarrier (model)

mutual
 def effects : Expr → List Nat
 | .source t => rowReads t
 | .primitive _ args | .nominal _ args => effectsMany args
 | .record _ a b | .join a b => effects a ++ effects b
 | .variant _ p => effects p
 def effectsMany : List Expr → List Nat
 | [] => []
 | x :: xs => effects x ++ effectsMany xs
end

mutual
 theorem local_eval (e : Expr) (a b : Assignment)
   (types : ∀ n ∈ support e, (a n).1 = (b n).1)
   (rows : ∀ n ∈ effects e, (a n).2 = (b n).2) : eval a e = eval b e := by
  cases e with
  | source t => exact local_type_eval model a b t types rows
  | primitive c args | nominal c args => simp only [eval,local_eval_many args a b types rows]
  | record l x y | join x y => simp only [eval,
      local_eval x a b (fun n h => types n (List.mem_append_left _ h))
        (fun n h => rows n (List.mem_append_left _ h)),
      local_eval y a b (fun n h => types n (List.mem_append_right _ h))
        (fun n h => rows n (List.mem_append_right _ h))]
  | variant l p => simp only [eval,local_eval p a b types rows]
 theorem local_eval_many (es : List Expr) (a b : Assignment)
   (types : ∀ n ∈ supports es, (a n).1 = (b n).1)
   (rows : ∀ n ∈ effectsMany es, (a n).2 = (b n).2) : evals a es = evals b es := by
  cases es with
  | nil => rfl
  | cons e es => simp only [evals,
      local_eval e a b (fun n h => types n (List.mem_append_left _ h))
        (fun n h => rows n (List.mem_append_left _ h)),
      local_eval_many es a b (fun n h => types n (List.mem_append_right _ h))
        (fun n h => rows n (List.mem_append_right _ h))]
end

def equationRows (e : Equation) := rowReads e.target ++ effects e.expression

theorem equation_iff (e : Equation) (a b : Assignment)
   (types : ∀ n ∈ equationReads e, (a n).1 = (b n).1)
   (rows : ∀ n ∈ equationRows e, (a n).2 = (b n).2) :
   e.Holds a ↔ e.Holds b := by
 simp only [Equation.Holds,local_type_eval model a b e.target
   (fun n h => types n (List.mem_append_left _ h)) (fun n h => rows n (List.mem_append_left _ h)),
   local_eval e.expression a b
   (fun n h => types n (List.mem_append_right _ h)) (fun n h => rows n (List.mem_append_right _ h))]

end Yulang.GeneralRebaseFiniteRowReads285
