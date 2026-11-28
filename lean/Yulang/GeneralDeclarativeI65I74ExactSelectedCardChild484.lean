import Yulang.GeneralDeclarativeI65I74TypedFocusHop482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read Args Fields)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row)

theorem checked_argument_card_restricts_to_the_exact_independently_typed_child
    {s : GeneralDeclarativeHead320.State} {t : Table} {mode : Mode}
    {raw code : List Expr} {w : ReadCards} {checked : ArgsRun s t mode raw code}
    (typed : checkedArgs s t mode raw code w = some checked) (index : Nat) {a b : Expr}
    (left : raw[index]? = some a) (right : code[index]? = some b) :
    ∃ card seen, argumentCard w index = some card ∧
      runReadCard s t mode a b card = some seen ∧ Read (SourceExposure481.authoredView s t) mode a b seen := by
  induction raw generalizing code w index with
  | nil => simp at left
  | cons x xs ih =>
    cases code with
    | nil => simp at right
    | cons y ys =>
      cases w with
      | nil => cases typed
      | cons head more =>
        rw [checkedArgs] at typed
        cases ranOne : checkedRead s t mode x y head with
        | none => simp [ranOne,bind,Option.bind] at typed
        | some one =>
          cases ranTail : checkedArgs s t mode xs ys more with
          | none => simp [ranOne,ranTail,bind,Option.bind] at typed
          | some rear =>
            cases index with
            | zero =>
              have ax := Option.some.inj left
              have by_ := Option.some.inj right
              subst a; subst b
              exact ⟨head,one.seen,rfl,by simp [runReadCard,ranOne],one.valid⟩
            | succ i => exact ih ranTail i (by simpa using left) (by simpa using right)

theorem checked_field_card_restricts_to_the_first_exact_written_label
    {s : GeneralDeclarativeHead320.State} {t : Table} {mode : Mode}
    {raw code : Row Expr} {w : ReadCards} {result : FieldsRun s t mode raw code}
    (typed : checkedFields s t mode raw code w = some result) (key : Nat) {a b : Expr}
    (left : raw.find? (fun x => x.1 == key) = some (key,a))
    (right : code.find? (fun x => x.1 == key) = some (key,b)) :
    ∃ card seen, fieldCard key code w = some card ∧
      runReadCard s t mode a b card = some seen ∧ Read (SourceExposure481.authoredView s t) mode a b seen := by
  induction raw generalizing code w with
  | nil => cases left
  | cons x xs ih =>
    cases code with
    | nil => cases right
    | cons y ys =>
      cases w with
      | nil => cases typed
      | cons head more =>
        obtain ⟨source,a'⟩ := x
        obtain ⟨dest,b'⟩ := y
        rw [checkedFields] at typed
        split at typed
        · rename_i exactKey
          subst dest
          cases ranOne : checkedRead s t mode a' b' head with
          | none => simp [ranOne,bind,Option.bind] at typed
          | some got =>
            cases ranTail : checkedFields s t mode xs ys more with
            | none => simp [ranOne,ranTail,bind,Option.bind] at typed
            | some rest =>
              by_cases here : source = key
              · subst source
                simp only [List.find?_cons,beq_self_eq_true,Option.some.injEq,Prod.mk.injEq,true_and] at left right
                subst a; subst b
                exact ⟨head,got.seen,by simp [fieldCard],by simp [runReadCard,ranOne],got.valid⟩
              · have nextRaw : List.find? (fun x => x.1 == key) xs = some (key,a) := by simpa [here] using left
                have nextCode : List.find? (fun x => x.1 == key) ys = some (key,b) := by simpa [here] using right
                obtain ⟨card,uses,run,read,valid⟩ := ih ranTail nextRaw nextCode
                exact ⟨card,uses,by simpa [fieldCard,here] using run,read,valid⟩
        · cases typed

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
