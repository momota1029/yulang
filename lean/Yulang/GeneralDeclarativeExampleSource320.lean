import Yulang.GeneralDeclarativeLeaf320
import Yulang.GeneralDeclarativeAssembly320
import Yulang.GeneralDeclarationExamples

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 3500000
namespace Yulang.GeneralDeclarativeExampleSource320
open GeneralDeclarationExamples (constructors roles wrap containerChild wrap_checked)
open GeneralDeclarations (Declaration Equation Registry DeclarationChecked Checked)
open GeneralDeclarationPatterns
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeBounds319 (Bound)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty nominal)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev association : Equation := ⟨0,1,.var 0⟩
abbrev leaf : Declaration := ⟨3,2,[.var 0],[],[association],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[wrap,leaf]⟩
abbrev interp : Interpretation := ⟨fun _ => none,fun n => n == 0,fun _ _ => rfl⟩

theorem leaf_checked : DeclarationChecked constructors roles leaf := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro eq present
      cases List.mem_singleton.mp present
      exact ⟨none,rfl⟩
    · intro name body declared
      change (if name = 1 then some none else none) = some body at declared
      split at declared
      · rename_i found
        exact .inl ⟨association,List.mem_cons_self,found.symm⟩
      · cases declared
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  all_goals intro c present; cases present

theorem checked : Checked registry := ⟨by decide +kernel,by
  intro decl found
  rcases List.mem_cons.mp found with eq|tail
  · cases eq; exact wrap_checked
  · cases List.mem_singleton.mp tail; exact leaf_checked⟩

abbrev input : Capture := ⟨0,1,2⟩
def point (name : Nat) : Capture := ⟨name,name,name⟩
abbrev child : Demand := ⟨2,[point 3],[⟨1,5⟩]⟩
abbrev root : Demand := ⟨1,[input],[⟨0,6⟩]⟩
def capture (name : Nat) : Capture := if name = 0 then point 3 else point 5
abbrev nApp (name : Nat) : Expr := .nominal 0 [.variable name]
abbrev int : Ty := .base .int

/-- The source constraint state stores no equation at the actual root
center 1. The root uses both nominal endpoints to determine that center. -/
def state : State := ⟨⟨[],[(0,1),(1,2)]⟩,
  [⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,
    ⟨5,.variable 3⟩,⟨6,nApp 5⟩]⟩

def model : Assignment := fun n =>
  (if n ≤ 2 ∨ n = 6 then nominal 0 [.inl int] else int,Common.rowEmpty)

theorem valid : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair used
    change pair ∈ [(0,1),(1,2)] at used
    rcases List.mem_cons.mp used with rfl|tail
    · exact CommonNominalFullCarrier.subtype_refl _
    · cases List.mem_singleton.mp tail
      exact CommonNominalFullCarrier.subtype_refl _
  · intro eq used
    change eq ∈ [⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,
      ⟨5,.variable 3⟩,⟨6,nApp 5⟩] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem input_bounds : Bounds state input := ⟨.interval List.mem_cons_self,
  .interval (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

theorem point_bounds (name : Nat) : Bounds state (point name) := ⟨.refl _,.refl _⟩

theorem no_center_equation : ∀ eq ∈ state.equations, eq.left ≠ input.center := by
  intro eq used
  change eq ∈ [⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,
    ⟨5,.variable 3⟩,⟨6,nApp 5⟩] at used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end Yulang.GeneralDeclarativeExampleSource320
