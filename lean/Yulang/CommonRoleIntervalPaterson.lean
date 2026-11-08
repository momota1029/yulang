import Yulang.CommonRoleStablePaterson
import Yulang.CommonRoleIntervals

/-!
# Stable declaration descent for both interval endpoints

The declaration and every `where` template are the existing finite Forms.
A captured argument supplies two original endpoints. Each endpoint is
substituted independently and normalized by the existing idempotence pass;
no type between the endpoints is chosen. All requirements retain their
original role, order and shared endpoint substitution.

The real finite stable Paterson check implies strict decrease for both
endpoint lists, and hence for their combined size. Candidate capture and
interval reconciliation are separate operations; no matching oracle or
success assumption is used by this expansion theorem.
-/

namespace Yulang.CommonRoleIntervalPaterson

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)

abbrev Argument := CommonRoleIntervals.Interval Form
abbrev Substitution := Nat → Argument

def instantiate (binding : Substitution) (forms : List Form) : List Argument :=
  forms.map fun form =>
    ((form.subst (fun name => (binding name).1)).normalize,
      (form.subst (fun name => (binding name).2)).normalize)

def lower (arguments : List Argument) : List Roles.Term :=
  arguments.map (fun argument => argument.1.encode)

def upper (arguments : List Argument) : List Roles.Term :=
  arguments.map (fun argument => argument.2.encode)

def size (arguments : List Argument) : Nat := Roles.argsSize (lower arguments) + Roles.argsSize (upper arguments)

structure Goal where
  role : Nat
  arguments : List Argument
  deriving DecidableEq, Repr

def head (declaration : Declaration) (binding : Substitution) : Goal :=
  ⟨declaration.role, instantiate binding declaration.head⟩

def child (requirement : Nat × List Form) (binding : Substitution) : Goal :=
  ⟨requirement.1, instantiate binding requirement.2⟩

def expand (declaration : Declaration) (binding : Substitution) : List Goal :=
  declaration.requirements.map (fun requirement => child requirement binding)

@[simp] theorem instantiate_lower (binding : Substitution) (forms : List Form) :
    lower (instantiate binding forms) =
      CommonRoleStablePaterson.instantiated forms (fun name => (binding name).1) := by
  simp [lower, instantiate, CommonRoleStablePaterson.instantiated]

@[simp] theorem instantiate_upper (binding : Substitution) (forms : List Form) :
    upper (instantiate binding forms) =
      CommonRoleStablePaterson.instantiated forms (fun name => (binding name).2) := by
  simp [upper, instantiate, CommonRoleStablePaterson.instantiated]

/-- This holds for every actual accepted declaration and every pair of
endpoint substitutions. It does not replace the finite checker with an
assumed rank law. Every original `where` child is included. -/
theorem every_where_decreases (declaration : Declaration)
    (accepted : CommonRoleStablePaterson.check declaration = true)
    (binding : Substitution) (requirement : Nat × List Form)
    (member : requirement ∈ declaration.requirements) :
    size (child requirement binding).arguments < size (head declaration binding).arguments := by
  have first := (CommonRoleStablePaterson.check_sound declaration accepted requirement member
    (fun name => (binding name).1)).1
  have last := (CommonRoleStablePaterson.check_sound declaration accepted requirement member
    (fun name => (binding name).2)).1
  simpa only [size, child, head, instantiate_lower, instantiate_upper] using Nat.add_lt_add first last

end Yulang.CommonRoleIntervalPaterson
