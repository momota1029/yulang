import Yulang.GeneralDeclarativeK2Graph321
import Yulang.GeneralDeclarativeOrigins321

namespace Yulang.GeneralDeclarativeGraphRows321
open GeneralDeclarativeK2Graph321 (Shape View arguments aliasView Descends Path OnCycle)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def fields : Expr → Option (List (Nat × Nat))
  | .primitive .emptyRecord [] => some []
  | .record label (.variable child) tail => (fields tail).map ((label,child) :: ·)
  | _ => none

/-- The purely normalized, named-operand fragment. Open and unnormalized
rows do not fabricate payload edges; "none" is not a K2 verdict. -/
def shapeOf : Expr → Option Shape
  | .primitive ctor args => (arguments args).map (.primitive ctor)
  | .nominal ctor args => (arguments args).map (.nominal ctor)
  | code@(.record _ _ _) => (fields code).map .record
  | .variant tag (.variable child) => some (.variant tag child)
  | _ => none

def observed (s : State) : View :=
  fun name shape => ∃ exp, (⟨name,exp⟩ : Equation) ∈ s.equations ∧ shapeOf exp = some shape

def structural (s : State) : View := aliasView s (observed s)

theorem literal_head (found : (⟨name,exp⟩ : Equation) ∈ s.equations)
    (shape : shapeOf exp = some head) : structural s name head :=
  ⟨name,GeneralDeclarativeLowerKnown321.alias_refl name,exp,found,shape⟩

theorem pending_nominal_self_cycle (p : Supported s completed) (owner : Nat)
    (establishes : p.derivesFrom ⟨name,.nominal tag [.variable name]⟩ (.output owner)) :
    OnCycle (structural s) name := by
  refine ⟨name,⟨.nominal tag [name],literal_head (p.ordinary establishes) rfl,?_⟩,.refl _⟩
  exact List.mem_cons_self

theorem supported_structure_subset (p : Supported s completed) :
    ∀ name head, structural (restriction p) name head → structural s name head := by
  intro name head observation
  obtain ⟨source,alias,exp,present,shape⟩ := observation
  have original : (restriction p).equations ⊆ s.equations := by
    intro row present
    exact
      p.ordinary ((backed_iff p row).mp present).choose_spec.1
  exact ⟨source, GeneralDeclarativeLowerKnown321.alias_mono (s := restriction p) (t := s) rfl original alias,
    exp,original present,shape⟩

/-- Dropping observational support cannot create a structural cycle. The
reverse inclusion is intentionally unavailable for provable pending outputs. -/
theorem supported_cycle_remains (p : Supported s completed)
    (cycle : OnCycle (structural (restriction p)) name) :
    OnCycle (structural s) name :=
  GeneralDeclarativeK2Graph321.closed_cycle_add_edges (supported_structure_subset p) cycle

end Yulang.GeneralDeclarativeGraphRows321
