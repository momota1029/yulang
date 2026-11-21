import Yulang.GeneralDeclarativeCompoundDecl325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundState325
open GeneralDeclarativeCompoundDecl325
open GeneralDeclarativeExampleSource320 (point int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty nominal subtype_refl)

abbrev rootArg : Capture := ⟨0,1,2⟩
abbrev childArg : Capture := ⟨8,9,10⟩
abbrev atom : Expr := .primitive (.scalar .int) []
abbrev openChild : Expr := .nominal 0 [.variable 3]
abbrev openRoot : Expr := .nominal 0 [.variable 7]
abbrev ordinaryRows : List Equation :=
  [⟨0,openRoot⟩,⟨2,openRoot⟩,⟨7,openChild⟩,⟨3,atom⟩,
    ⟨8,.variable 7⟩,⟨9,.variable 8⟩,⟨10,.variable 7⟩]
abbrev parentRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable 9⟩
abbrev initial : State := ⟨⟨[],[(0,1),(1,2),(8,9),(9,10)]⟩,ordinaryRows⟩
abbrev middle : State := appendFacts initial [parentRow]
abbrev final : State := appendFacts middle [childRow]

def support0 (done : Nat → Prop) : Supported initial done :=
  ⟨fun row origin => row ∈ ordinaryRows ∧ origin = .source,fun f => f.1⟩
def support1 (done : Nat → Prop) : Supported middle done := emit (support0 done) 1 [parentRow]
def support2 (done : Nat → Prop) : Supported final done := emit (support1 done) 2 [childRow]

theorem ordinary_old {row : Equation} (known : row ∈ ordinaryRows) : row ∈ final.equations :=
  List.mem_append_left _ (List.mem_append_left _ known)

theorem authorized (done : Nat → Prop) {row : Equation} (known : row ∈ ordinaryRows) :
    row ∈ (restriction (support2 done)).equations :=
  from_source _ (.inl (.inl ⟨known,rfl⟩))

theorem absence_of_center_row : ¬ ∃ rhs, (⟨1,rhs⟩ : Equation) ∈ final.equations := by
  rintro ⟨rhs,found⟩
  simp only [final,middle,appendFacts,ordinaryRows,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with h|h|h|h|h|h|h|h|h <;> have wrong := congrArg Equation.left h <;> cases wrong

theorem root_bounds : Bounds final rootArg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem child_bounds : Bounds final childArg :=
  ⟨.interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
   .interval (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem point_bounds (n : Nat) : Bounds final (point n) := ⟨.refl _,.refl _⟩

abbrev innerTy : Ty := nominal 0 [.inl int]
abbrev outerTy : Ty := nominal 0 [.inl innerTy]
def assign (fixed : Bool) : Assignment := fun n =>
  (if n ≤ 2 then outerTy else if n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 then innerTy else
    if n = 5 ∨ n = 6 then if fixed then innerTy else .top else int,Common.rowEmpty)

theorem initial_model (fixed : Bool) : Models initial (assign fixed) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro link found
    change link ∈ [(0,1),(1,2),(8,9),(9,10)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro row found
    change row ∈ ordinaryRows at found
    simp only [ordinaryRows,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem middle_model (fixed : Bool) : Models middle (assign fixed) := by
  apply (model_append _).mpr
  refine ⟨initial_model fixed,?_⟩
  intro row found
  cases List.mem_singleton.mp found
  cases fixed <;> exact eqv_refl _

theorem inhabited : Models final (assign true) := by
  apply (model_append _).mpr
  refine ⟨middle_model true,?_⟩
  intro row found
  cases List.mem_singleton.mp found
  exact eqv_refl _

theorem two_ordinary_applications (m : Assignment) : Models final m ↔
    Models initial m ∧ Holds m parentRow ∧ Holds m childRow := by
  rw [model_append,model_append]
  simp [and_assoc]

end Yulang.GeneralDeclarativeCompoundState325
