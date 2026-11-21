import Yulang.GeneralDeclarativeHiddenDecl324
import Yulang.GeneralDeclarativeRepeat320
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeExampleSource320 (point leaf int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEntailment320 (Entails Holds literal appendFacts model_append)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeNormalizeAssoc324 (one row_iff)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Ty record emptyRecord)
open GeneralNominalCommonBridge (Assignment)

abbrev root : Demand := ⟨1,[point 0],[⟨0,6⟩]⟩
abbrev child : Demand := ⟨2,[point 3],[⟨1,5⟩]⟩
abbrev names : Names := ⟨fun n => point (if n = 0 then 3 else 5),fun _ => 5⟩
abbrev leafNames : Names := ⟨fun _ => point 3,fun _ => 3⟩
abbrev place : Placement := ⟨fun _ _ => point 400,fun _ _ => 401⟩
abbrev direct : Expr := .record 7 (.variable 3) empty
abbrev opened : Expr := .record 7 (.variable 3) (.variable 2)
abbrev s0Rows : List Equation :=
  [⟨0,direct⟩,⟨0,opened⟩,⟨2,empty⟩,⟨3,.primitive (.scalar .int) []⟩]
abbrev parentRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable 3⟩
def initial : State := ⟨⟨[],[]⟩,s0Rows⟩
def afterParent : State := appendFacts initial [parentRow]
def final : State := appendFacts afterParent [childRow]
abbrev finalRows : List Equation := s0Rows ++ [parentRow] ++ [childRow]

theorem exact_child : children parent names place = [child] := rfl

theorem root_rule :
    collect (one registry interpretation parent root names.input) root.outputs = some [parentRow] := rfl

theorem child_rule :
    collect (one registry interpretation leaf child leafNames.input) child.outputs = some [childRow] := rfl

theorem parent_rows_iff (row : Equation) :
    SourceEquation registry interpretation root parent names.input row ↔ row = parentRow := by
  rw [row_iff checked List.mem_cons_self]
  constructor
  · rintro ⟨out,member,emitted⟩
    cases List.mem_singleton.mp member
    have same : some [parentRow] = some [row] := emitted
    exact (List.cons.inj (Option.some.inj same)).1.symm
  · rintro rfl
    exact ⟨⟨0,6⟩,List.mem_cons_self,rfl⟩

theorem child_rows_iff (row : Equation) :
    SourceEquation registry interpretation child leaf leafNames.input row ↔ row = childRow := by
  rw [row_iff checked (List.mem_cons_of_mem _ List.mem_cons_self)]
  constructor
  · rintro ⟨out,member,emitted⟩
    cases List.mem_singleton.mp member
    have same : some [childRow] = some [row] := emitted
    exact (List.cons.inj (Option.some.inj same)).1.symm
  · rintro rfl
    exact ⟨⟨1,5⟩,List.mem_cons_self,rfl⟩

theorem stable_root : StableUnder final (SourceEquation registry interpretation root parent names.input) := by
  apply stable_exact.mpr
  intro row rule
  cases (parent_rows_iff row).mp rule
  exact literal (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))

theorem stable_child : StableUnder final (SourceEquation registry interpretation child leaf leafNames.input) := by
  apply stable_exact.mpr
  intro row rule
  cases (child_rows_iff row).mp rule
  exact literal (List.mem_append_right _ List.mem_cons_self)

def sourceSupport (completed : Nat → Prop) : Supported initial completed :=
  ⟨fun row origin => row ∈ s0Rows ∧ origin = .source, fun h => h.1⟩

def support (completed : Nat → Prop) : Supported final completed :=
  emit (emit (sourceSupport completed) 1 [parentRow]) 2 [childRow]

abbrev regularRecord : Ty := record 7 int emptyRecord
def assignment (known : Bool) : Assignment := fun n =>
  (if n = 0 then regularRecord else if n = 2 then emptyRecord
   else if (n = 5 ∨ n = 6) ∧ known = false then .top else int,Common.rowEmpty)

theorem fits_initial (known : Bool) : Models initial (assignment known) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ never => False.elim (List.not_mem_nil never)⟩,?_⟩
  intro row used
  change row ∈ s0Rows at used
  simp only [s0Rows,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl
  all_goals cases known <;> exact eqv_refl _

theorem parent_only_fits (known : Bool) : Models afterParent (assignment known) :=
  (model_append _).mpr ⟨fits_initial known,fun _ mem => by
    cases List.mem_singleton.mp mem
    cases known <;> exact eqv_refl _⟩

theorem fits_final : Models final (assignment true) :=
  (model_append _).mpr ⟨parent_only_fits true,fun _ mem => by
    cases List.mem_singleton.mp mem
    exact eqv_refl _⟩

theorem parent_not_enough : ¬Models final (assignment false) := by
  intro impossible
  have found := ((model_append _).mp impossible).2 childRow List.mem_cons_self
  exact GeneralDeclarativeRepeat320.top_not_int found.1

theorem final_models (m : Assignment) :
    Models final m ↔ Models initial m ∧ Holds m parentRow ∧ Holds m childRow := by
  rw [final,afterParent,model_append,model_append]
  simp [and_assoc]

end Yulang.GeneralDeclarativeHiddenState324
