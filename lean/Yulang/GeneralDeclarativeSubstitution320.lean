import Yulang.GeneralDeclarativePoint320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 2800000
namespace Yulang.GeneralDeclarativeSubstitution320
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Read byMode environment variables_eq read_sound)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)

mutual
 def logical (capture : Nat → Capture) (mode : Mode) : Expr → Expr
  | .variable name => .variable (byMode (capture name) mode)
  | .primitive ctor args => .primitive ctor (logicals capture mode args)
  | .nominal name args => .nominal name (logicals capture .actual args)
  | .record label payload tail => .record label (logical capture mode payload) (logical capture mode tail)
  | .variant label payload => .variant label (logical capture mode payload)
  | .join a b => .join (logical capture mode a) (logical capture mode b)

 def logicals (capture : Nat → Capture) (mode : Mode) : List Expr → List Expr
  | [] => []
  | one :: more => logical capture mode one :: logicals capture mode more
end

mutual
 theorem logical_value (capture : Nat → Capture) (m : Assignment) (mode evalMode : Mode) (e : Expr) :
    value (environment m) evalMode (logical capture mode e) = value (variables capture m) mode e := by
  cases e with
  | «variable» name =>
    simp only [logical,value,environment]
    exact (variables_eq capture m mode name).symm
  | primitive ctor args =>
    simp only [logical,value,logical_values capture m mode evalMode args]
  | nominal name args =>
    simp only [logical,value,logical_values capture m .actual .actual args]
  | record label payload tail =>
    simp only [logical,value,logical_value capture m mode evalMode payload,
      logical_value capture m mode evalMode tail]
  | variant label x =>
    simp only [logical,value,logical_value capture m mode evalMode x]
  | join a b =>
    simp only [logical,value,logical_value capture m mode evalMode a,
      logical_value capture m mode evalMode b]
 termination_by sizeOf e
 theorem logical_values (capture : Nat → Capture) (m : Assignment) (mode evalMode : Mode) (es : List Expr) :
    values (environment m) evalMode (logicals capture mode es) = values (variables capture m) mode es := by
  cases es with
  | nil => rfl
  | cons e es =>
    simp only [logicals,values,logical_value capture m mode evalMode e,
      logical_values capture m mode evalMode es]
 termination_by sizeOf es
end

/-- A single stored ordinary compound equation suffices; no logical names
for its proper subexpressions need to have been introduced. -/
inductive EquationRead (s : State) (capture : Nat → Capture) : Mode → Nat → Expr → Prop where
  | structural : Read s capture mode name code → EquationRead s capture mode name code
  | whole : ⟨name,logical capture mode code⟩ ∈ s.equations →
      EquationRead s capture mode name code

theorem equation_read {s capture mode name code}
    (derived : EquationRead s capture mode name code) (m : Assignment) (valid : Models s m) :
    Equivalent (m name).1 (value (variables capture m) mode code) := by
  cases derived with
  | structural deriv => exact read_sound deriv m valid
  | whole read =>
    have recorded := valid.2 _ read
    rw [logical_value] at recorded
    exact recorded

end Yulang.GeneralDeclarativeSubstitution320
