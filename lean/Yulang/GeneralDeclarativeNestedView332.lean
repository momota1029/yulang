import Yulang.GeneralDeclarativeNestedSyntax332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedView332
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)

/-- An index into actual supported rows is not a semantic oracle.
A witnessed name expansion must point at a stored RHS and an
authorized alias to its recorded owner. No present model is read. -/
structure Sources (s : State) where
  visible : Nat → Option Expr
  authorized : ∀ n rhs, visible n = some rhs →
    ∃ owner, Alias s n owner ∧ (⟨owner,rhs⟩ : Equation) ∈ s.equations
  spines : Nat → Option (Row Expr × Expr)
  spine_sound : ∀ n raw tail, spines n = some (raw,tail) → Spine s n raw tail

def literalRows (named : Nat → Option (Row Expr × Expr)) : Expr → Option (Row Expr × Expr)
  | .variable n => named n
  | .record key data tail =>
    (literalRows named tail).map fun (rows,term) => ((key,data)::rows,term)
  | .primitive .emptyRecord [] => some ([],.primitive .emptyRecord [])
  | .primitive .exactEmpty [] => some ([],.primitive .exactEmpty [])
  | _ => none

theorem literalRows_sound {s : State} (src : Sources s) (input : Expr)
    (seen : literalRows src.spines input = some (row,terminal)) :
    Closed s input row terminal := by
  cases input with
  | «variable» n => exact .name (src.spine_sound _ _ _ seen)
  | record label payload tail =>
    cases got : literalRows src.spines tail with
    | none => simp [literalRows,got] at seen
    | some values =>
      obtain ⟨fields,ending⟩ := values
      have same : ((label,payload)::fields,ending) = (row,terminal) := by
        simpa [literalRows,got] using seen
      cases same
      exact .field (literalRows_sound src tail got)
  | primitive tag args =>
    cases tag <;> cases args <;> simp [literalRows] at seen
    all_goals obtain ⟨rfl,rfl⟩ := seen
    · exact .terminal .width
    · exact .terminal .exactEnd
  | nominal | variant | join => cases seen

termination_by structural input
def expand (src : Sources s) : Expr → Expr
  | .variable n => (src.visible n).getD (.variable n)
  | raw => raw

theorem expand_is {s : State} (src : Sources s) (input : Expr) :
    expand src input = input ∨ ∃ n owner, input = .variable n ∧
      Alias s n owner ∧ (⟨owner,expand src input⟩ : Equation) ∈ s.equations := by
  cases input with
  | «variable» n =>
    cases res : src.visible n with
    | none => exact .inl (by simp [expand,res])
    | some rhs =>
      obtain ⟨owner,linked,found⟩ := src.authorized n rhs res
      exact .inr ⟨n,owner,rfl,linked,by simpa [expand,res] using found⟩
  | primitive | nominal | record | variant | join => exact .inl rfl

end Yulang.GeneralDeclarativeNestedView332
