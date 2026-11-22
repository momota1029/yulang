import Yulang.GeneralDeclarativeWitnessReceipt349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReceiptFixture349
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessReceipt349 (Plan verify same_model)
open GeneralDeclarativeWitnessEquation349 (Code)
open GeneralDeclarativeWitnessLiteral349 (preserves)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty exactEmpty record variant subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev stop : Expr := .primitive .exactEmpty []
def expr (n : Nat) : Expr := .record 7 (.variant 3 (.variable n)) stop
def oldAtom : PresenceNormalForm.Atom Nat := .tyLe (.var 2) (.var 6)
def current : State := ⟨⟨[oldAtom],[(0,2)]⟩,[⟨76,expr 2⟩,⟨2,.variable 5⟩]⟩
def expected : State := ⟨⟨[oldAtom],[(0,6)]⟩,[⟨76,expr 5⟩]⟩

def eqCode : Code :=
  .compose (.currentRow 0) (.record 7 (.variant 3 (.currentRow 1)) (.refl stop))

def receipt : Plan := ⟨[0],[.compose (.interval 0) (.constraint 0)],[eqCode]⟩

theorem semantic_not_literal :
    verify expected current receipt = true ∧ preserves expected current = false := by decide +kernel

theorem wrong_middle :
    verify expected current {receipt with equations :=
      [.compose (.currentRow 0) (.record 7 (.variant 3 (.refl (.variable 5))) (.refl stop))]} = false := by
  decide +kernel

theorem wrong_atom_slot :
    verify expected current {receipt with atoms := [1]} = false := rfl

def scalar : Ty := .base .int
def model : Assignment := fun n =>
  (if n = 76 then record 7 (variant 3 scalar) exactEmpty else scalar, Common.rowEmpty)

theorem current_model : Models current model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a h
    change a ∈ [oldAtom] at h
    cases List.mem_singleton.mp h
    exact subtype_refl _
  · intro x used
    change x ∈ [(0,2)] at used
    cases List.mem_singleton.mp used
    exact subtype_refl _
  · intro e listed
    change e ∈ [⟨76,expr 2⟩,⟨2,.variable 5⟩] at listed
    rcases List.mem_cons.mp listed with same|other
    · cases same
      exact eqv_refl _
    · cases List.mem_singleton.mp other
      exact eqv_refl _

theorem nonvacuous_transport : Models current model ∧ Models expected model :=
  ⟨current_model,same_model semantic_not_literal.1 _ current_model⟩

end Yulang.GeneralDeclarativeWitnessReceiptFixture349
