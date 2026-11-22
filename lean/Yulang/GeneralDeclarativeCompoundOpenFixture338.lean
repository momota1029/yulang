import Yulang.GeneralDeclarativeCompoundOpenReceipt338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundOpenFixture338
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source backed_iff)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeCompoundOpenPrefix338 (Read residuals)
open GeneralDeclarativeCompoundOpenReceipt338 (exact_named)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record exactEmpty subtype_refl)

abbrev a : Capture := ⟨0,1,2⟩
abbrev raw : Expr := .record 7 (.variable 3) (.variable 4)
abbrev lhs : Equation := ⟨0,raw⟩
abbrev rhs : Equation := ⟨2,raw⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev s : State := ⟨⟨[],[(0,1),(1,2)]⟩,[lhs,rhs,scalar]⟩
def p : Supported s (fun _ => False) :=
  ⟨fun eq o => eq ∈ s.equations ∧ o = .source,And.left⟩
abbrev fields : List (Nat × Expr) := [(7,.variable 3)]

theorem supported {q : Equation} (h : q ∈ s.equations) : q ∈ (restriction p).equations :=
  from_source _ ⟨h,rfl⟩

theorem read_prefix : Read p a [7] fields fields fields fields (.variable 4) (.variable 4) :=
  ⟨⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
    ⟨⟨0,alias_refl _,supported List.mem_cons_self⟩,
     ⟨2,alias_refl _,supported (List.mem_cons_of_mem _ List.mem_cons_self)⟩⟩,
    by decide,rfl,rfl⟩

theorem bound_le (h : Bound (restriction p).normal x y) : x ≤ y := by
  induction h with
  | interval seen =>
    change _ ∈ [(0,1),(1,2)] at seen
    rcases List.mem_cons.mp seen with eq|rest
    · cases eq; decide
    · cases List.mem_singleton.mp rest; decide
  | constraint seen => exact False.elim (List.not_mem_nil seen)
  | refl => exact Nat.le_refl _
  | trans _ _ first last => exact Nat.le_trans first last

theorem originally {q} (h : q ∈ (restriction p).equations) : q ∈ s.equations :=
  p.ordinary ((backed_iff p q).mp h).choose_spec.1

theorem alias_only_self (h : Alias (restriction p) x y) : x = y := by
  have noAlias {u v} (seen : (⟨u,.variable v⟩ : Equation) ∈ s.equations) : False := by
    change (⟨u,.variable v⟩ : Equation) ∈ [lhs,rhs,scalar] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with bad|bad|bad <;> cases bad
  induction h with
  | bounds one two => exact Nat.le_antisymm (bound_le one) (bound_le two)
  | forward old => exact (noAlias (originally old)).elim
  | backward old => exact (noAlias (originally old)).elim
  | trans _ _ first last => exact first.trans last

theorem no_row_four {e} : (⟨4,e⟩ : Equation) ∉ (restriction p).equations := by
  intro authored
  have old := originally authored
  change (⟨4,e⟩ : Equation) ∈ [lhs,rhs,scalar] at old
  simp only [List.mem_cons,List.not_mem_nil,or_false] at old
  rcases old with bad|bad|bad <;> cases bad

theorem tail_not_closed (seen : Closed (restriction p) (.variable 4) rest term) : False := by
  cases seen with
  | terminal t => cases t
  | name spine =>
    cases spine with
    | width a b | exactEnd a b | cons a b _ | inline a _ b | prefixed a b _ =>
      have out := alias_only_self a
      exact no_row_four (out.symm ▸ b)

def model : Assignment := fun n =>
  (if n < 3 then record 7 int (record 7 int exactEmpty)
    else if n = 4 then record 7 int exactEmpty else int,Common.rowEmpty)

theorem source_valid : Models s model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e used
    change e ∈ [(0,1),(1,2)] at used
    rcases List.mem_cons.mp used with eq|rest
    · cases eq; exact subtype_refl _
    · cases List.mem_singleton.mp rest; exact subtype_refl _
  · intro e used
    change e ∈ [lhs,rhs,scalar] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl <;> exact eqv_refl _

/-- The scenario really has a backed visible prefix and a fitting
model, but *no* supported closure of its tail. Exact deletion hides the
tail's shadow without reusing the tail as an authored residual. -/
theorem unknown_prefix_fixture :
    Models s model ∧ (¬ ∃ r endTerm, Closed (restriction p) (.variable 4) r endTerm) ∧
      (residuals [7] model a).2.1 = exactEmpty :=
  ⟨source_valid,by rintro ⟨r,endTerm,h⟩; exact tail_not_closed h,rfl⟩

end Yulang.GeneralDeclarativeCompoundOpenFixture338
