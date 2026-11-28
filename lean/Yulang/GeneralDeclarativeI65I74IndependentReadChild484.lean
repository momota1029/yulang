import Yulang.GeneralDeclarativeI65I74TypedFocusHop482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeInlineTrace331 (Read Args Fields)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row)

theorem declarative_argument_read_projects_the_exact_requested_child
    {s : GeneralDeclarativeHead320.State} {m : Mode}
    {raw code : List Expr} {uses} (root : Args s m raw code uses)
    (ix : Nat) {one other : Expr}
    (pre : raw[ix]? = some one) (post : code[ix]? = some other) :
    ∃ childUses, Read s m one other childUses := by
  induction raw generalizing code uses ix with
  | nil => simp at pre
  | cons x xs ih =>
    cases root with
    | cons first rest =>
      cases ix with
      | zero =>
        have source := Option.some.inj pre
        have dest := Option.some.inj post
        subst one; subst other
        exact ⟨_,first⟩
      | succ i =>
        exact ih rest i (by simpa using pre) (by simpa using post)

theorem declarative_field_read_projects_the_first_requested_label
    {s : GeneralDeclarativeHead320.State} {m : Mode}
    {raw code : Row Expr} {uses} (root : Fields s m raw code uses)
    (key : Nat) {one other : Expr}
    (pre : raw.find? (fun x => x.1 == key) = some (key,one))
    (post : code.find? (fun x => x.1 == key) = some (key,other)) :
    ∃ childUses, Read s m one other childUses := by
  induction raw generalizing code uses with
  | nil => cases pre
  | cons x xs ih =>
    cases root with
    | @cons _ _ _ _ _ _ _ label first tail =>
      by_cases selected : label = key
      · subst label
        simp only [List.find?_cons,beq_self_eq_true,Option.some.injEq,Prod.mk.injEq,true_and] at pre post
        subst one; subst other
        exact ⟨_,first⟩
      · exact ih tail (by simpa [selected] using pre) (by simpa [selected] using post)

/-- The independent child derivation yields reusable finite data in the
same old authored table. Nothing about an ambient alternative's authority
is inferred; this reads only the fixed selected operands. -/
theorem selected_declarative_field_supplies_a_complete_typed_finite_child_card
    {s : GeneralDeclarativeHead320.State} {t : Table} {m : Mode}
    {raw code : Row Expr} {uses}
    (attach : Attached s t) (root : Fields (SourceExposure481.authoredView s t) m raw code uses)
    (key : Nat) {one other : Expr}
    (pre : raw.find? (fun x => x.1 == key) = some (key,one))
    (post : code.find? (fun x => x.1 == key) = some (key,other)) :
    ∃ childUses childCard, runReadCard s t m one other childCard = some childUses ∧
      Read (SourceExposure481.authoredView s t) m one other childUses := by
  obtain ⟨seen,read⟩ := declarative_field_read_projects_the_first_requested_label root key pre post
  obtain ⟨child,w⟩ := full_c331_authored_read_has_finite_card attach read
  exact ⟨seen,child,w,read⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
