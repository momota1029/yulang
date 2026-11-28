import Yulang.GeneralDeclarativeI65I74IndependentNamedChild484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open SourceExposure481 (authoredView notBinder notBinder_exact)
open CommonRoleCanonicalRows (Row)

private theorem closed_prefix_keeps_same_fields
    {s : GeneralDeclarativeHead320.State} {rest endAt : Expr} {row : Row Expr}
    (read : Closed s rest row endAt) (front : Row Expr) :
    Closed s (withTail front rest) (front++row) endAt := by
  induction front with
  | nil => exact read
  | cons field next ih =>
    cases field
    exact .field ih

theorem first_named_spine_layer_has_a_literal_authorized_equation_and_a_residual_read
    {s : GeneralDeclarativeHead320.State} {name : Nat} {row : Row Expr} {endAt : Expr}
    (read : Spine s name row endAt) :
    ∃ stored : Equation, stored ∈ s.equations ∧
      GeneralDeclarativeLowerKnown321.Alias s name stored.left ∧ Closed s stored.right row endAt := by
  cases read with
  | width alias present => exact ⟨_,present,alias,.terminal .width⟩
  | exactEnd alias present => exact ⟨_,present,alias,.terminal .exactEnd⟩
  | cons alias present next => exact ⟨_,present,alias,.field (.name next)⟩
  | inline alias leaf present => exact ⟨_,present,alias,by simpa only [List.append_nil] using closed_prefix_keeps_same_fields (.terminal leaf) row⟩
  | prefixed alias present next => exact ⟨_,present,alias,closed_prefix_keeps_same_fields (.name next) _⟩

/-- One layer of the independent authored read. For a C331 record proof it
peels the first proved closed-spine equation, not a geometrically chosen row. -/
theorem named_nonbinder_original_read_peels_one_authorized_row
    {s : GeneralDeclarativeHead320.State} {name : Nat} {code : Expr} {mode uses}
    (inspect : ∀ a, code ≠ .variable a)
    (known : Read s mode (.variable name) code uses) :
    ∃ stored : Equation, stored ∈ s.equations ∧
      GeneralDeclarativeLowerKnown321.Alias s name stored.left ∧ Read s mode stored.right code uses := by
  cases known with
  | capture => exact False.elim (inspect _ rfl)
  | expose _ alias selected child => exact ⟨_,selected,alias,child⟩
  | record closed unique nonempty order fields tail child =>
    cases closed with
    | terminal impossible => cases impossible
    | name spine =>
      obtain ⟨stored,existsOld,near,residue⟩ := first_named_spine_layer_has_a_literal_authorized_equation_and_a_residual_read spine
      exact ⟨stored,existsOld,near,.record residue unique nonempty order fields tail child⟩

theorem named_nonbinder_original_read_extracts_its_finite_first_layer_and_residual_card
    {s : GeneralDeclarativeHead320.State} {table : Table} {name : Nat} {code : Expr} {mode uses}
    (attach : Attached s table) (inspect : notBinder code = true)
    (known : Read (authoredView s table) mode (.variable name) code uses) :
    ∃ stored : Equation, ∃ w : ExposureWire, ∃ card : ReadCard,
      readExposure s table name code w = some stored ∧
      runReadCard s table mode stored.right code card = some uses ∧
      Read (authoredView s table) mode stored.right code uses := by
  have notOne : ∀ a, code ≠ .variable a := (notBinder_exact _).mp inspect
  obtain ⟨stored,present,near,rest⟩ := named_nonbinder_original_read_peels_one_authorized_row notOne known
  obtain ⟨w,pinned⟩ := every_independent_authored_alias_exposure_has_finite_index_data
    (row := stored) (code := code) attach present notOne near
  obtain ⟨card,ready⟩ := full_c331_authored_read_has_finite_card attach rest
  exact ⟨stored,w,card,pinned,ready,rest⟩


private theorem direct_row_when_spine_just_names_another_row
    {s : GeneralDeclarativeHead320.State} {name : Nat} {row : Row Expr} {endAt : Expr}
    (read : Spine s name row endAt) :
    ∃ stored : Equation, stored ∈ s.equations ∧ GeneralDeclarativeLowerKnown321.Alias s name stored.left ∧
      (∀ x, stored.right ≠ .variable x) ∧ Closed s stored.right row endAt := by
  induction read with
  | width near found =>
    exact ⟨_,found,near,(by intro x no; cases no),.terminal .width⟩
  | exactEnd near found =>
    exact ⟨_,found,near,(by intro x no; cases no),.terminal .exactEnd⟩
  | cons near found after _ =>
    exact ⟨_,found,near,(by intro x no; cases no),.field (.name after)⟩
  | @inline root owner leaf front near stop found =>
    refine ⟨_,found,near,?_,by simpa using (closed_prefix_keeps_same_fields (.terminal stop) front)⟩
    cases front with
    | nil => intro x no; cases stop <;> cases no
    | cons f rest => cases f; intro x no; cases no
  | @prefixed root owner front rest suffix leaf near found after ih =>
    cases front with
    | nil =>
      obtain ⟨row,stored,atEnd,shape,done⟩ := ih
      exact ⟨row,stored,.trans near (.trans (.forward found) atEnd),shape,done⟩
    | cons head more =>
      rcases head with ⟨label,value⟩
      exact ⟨_,found,near,(by intro x bad; cases bad),closed_prefix_keeps_same_fields (.name after) ((label,value)::more)⟩

/-- Pure exposure steps may be skipped via actual old aliases in source
evidence. The chosen non-variable row and its residual typing remain
in the same supported source view, independently of ambient geometry. -/
theorem original_named_read_reaches_a_real_nonvariable_author_row
    {s : GeneralDeclarativeHead320.State} {name : Nat} {code : Expr} {mode uses}
    (inspect : ∀ x, code ≠ .variable x) (known : Read s mode (.variable name) code uses) :
    ∃ row : Equation, row ∈ s.equations ∧ GeneralDeclarativeLowerKnown321.Alias s name row.left ∧
      (∀ x, row.right ≠ .variable x) ∧ Read s mode row.right code uses := by
  let target := fun m raw code seen (_ : Read s m raw code seen) =>
    ∀ name, raw = .variable name → (∀ x, code ≠ .variable x) →
      ∃ row : Equation, row ∈ s.equations ∧ GeneralDeclarativeLowerKnown321.Alias s name row.left ∧
        (∀ x, row.right ≠ .variable x) ∧ Read s m row.right code seen
  refine Read.rec (motive_1 := target)
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ known name rfl inspect
  · intro m raw binder site hit notVar
    exact False.elim (notVar binder rfl)
  · intro code prior owner raw uses mode _ near found child ih site hit live
    obtain rfl := Expr.variable.inj hit
    cases h : raw with
    | «variable» next =>
      obtain ⟨row,haveRow,atRow,shape,body⟩ := ih next h live
      have forward : GeneralDeclarativeLowerKnown321.Alias s owner next := .forward (h ▸ found)
      exact ⟨row,haveRow,.trans near (.trans forward atRow),shape,body⟩
    | _ =>
      all_goals
        refine ⟨⟨owner,raw⟩,found,near,?_,child⟩
        intro x impossible
        change raw = .variable x at impossible
        rw [h] at impossible
        cases impossible
  · intro _ _ _ _ _ _ _ _ no
    cases no
  · intro _ _ _ _ _ _ _ _ no
    cases no
  · intro _ _ _ _ _ _ _ _ no
    cases no
  · intro _ _ _ _ _ _ _ _ _ _ _ _ no
    cases no
  · intro input raw terminal keys selected mode written first tailCode last spine unique haveKeys order
      typing legal tailRead _ _ name original _
    subst input
    cases spine with
    | terminal nope => cases nope
    | name expanded =>
      obtain ⟨row,old,near,shape,parent⟩ := direct_row_when_spine_just_names_another_row expanded
      exact ⟨row,old,near,shape,.record parent unique haveKeys order typing legal tailRead⟩
  all_goals intros; trivial

theorem original_nonbinder_read_reifies_a_direct_author_row_and_the_same_independent_read
    {s : GeneralDeclarativeHead320.State} {table : Table} {name : Nat} {code : Expr} {mode uses}
    (attach : Attached s table) (inspect : notBinder code = true)
    (known : Read (authoredView s table) mode (.variable name) code uses) :
    ∃ row : Equation, ∃ w : ExposureWire, ∃ card : ReadCard,
      readExposure s table name code w = some row ∧
      ObservationSyntax471.isDefinedAt row.left row = true ∧
      runReadCard s table mode row.right code card = some uses ∧
      Read (authoredView s table) mode row.right code uses := by
  have notVar : ∀ x, code ≠ .variable x := (notBinder_exact _).mp inspect
  obtain ⟨row,existsOld,near,shape,parent⟩ :=
    original_named_read_reaches_a_real_nonvariable_author_row notVar known
  obtain ⟨w,physical⟩ := every_independent_authored_alias_exposure_has_finite_index_data
    (row := row) (code := code) attach existsOld notVar near
  obtain ⟨card,typed⟩ := full_c331_authored_read_has_finite_card attach parent
  refine ⟨row,w,card,physical,?_,typed,parent⟩
  cases h : row.right <;> simp [ObservationSyntax471.isDefinedAt,h]
  exact False.elim (shape _ h)

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
