import Yulang.GeneralSourceMetadataBundlePermutation291

/-! Executable bootstrapping from resolved data; any proof of positional
default scope is obtained by the check, not required from the caller. -/
namespace Yulang.GeneralSourceMetadataBareRole291
open GeneralSourceMetadataRoles291 (RoleRow)
open GeneralSourceMetadataExprDomain291 (two_success)

structure BareRow where
  role : Nat
  arity : Nat
  outputs : List (Nat × Option Roles.Term)

def forgetRow (row : RoleRow) : BareRow := ⟨row.role,row.arity,row.outputs⟩

def Scope (row : BareRow) : Prop :=
  ∀ name rhs, (name,some rhs) ∈ row.outputs → rhs.bound ≤ row.arity

def bounded (row : BareRow) : Bool :=
  row.outputs.all (fun out => match out.2 with
    | none => true
    | some rhs => decide (rhs.bound ≤ row.arity))

theorem bounded_exact (row : BareRow) : bounded row = true ↔ Scope row := by
  rw [bounded,List.all_eq_true]
  constructor
  · intro ready name rhs found
    exact of_decide_eq_true (ready (name,some rhs) found)
  · intro ready out member
    obtain ⟨name,value⟩ := out
    cases value with
    | none => rfl
    | some rhs => exact decide_eq_true_eq.mpr (ready name rhs member)

def refineRow (r : BareRow) (valid : Scope r) : RoleRow := ⟨r.role,r.arity,r.outputs,valid⟩

def buildRow (raw : BareRow) : Option RoleRow :=
  if checked : bounded raw = true then some (refineRow raw ((bounded_exact raw).mp checked))
  else none

theorem forget_refine (r : BareRow) (h : Scope r) : forgetRow (refineRow r h) = r := by
  cases r; rfl

theorem refine_forget (r : RoleRow) (h : Scope (forgetRow r)) : refineRow (forgetRow r) h = r := by
  cases r; rfl

theorem row_exact (raw : BareRow) (out : RoleRow) : buildRow raw = some out ↔ forgetRow out = raw := by
  constructor
  · intro result
    unfold buildRow at result
    by_cases valid : bounded raw = true
    · rw [dite_eq_left valid] at result
      cases Option.some.inj result
      exact forget_refine raw _
    · rw [dite_eq_right valid] at result
      cases result
  · rintro rfl
    have valid : bounded (forgetRow out) = true := (bounded_exact ..).mpr out.boundOK
    unfold buildRow
    rw [dite_eq_left valid,refine_forget]

def buildRows : List BareRow → Option (List RoleRow)
  | [] => some []
  | r :: rs => (buildRow r).bind fun h => (buildRows rs).bind fun t => some (h :: t)

theorem list_exact (data : List BareRow) (ready : List RoleRow) :
    buildRows data = some ready ↔ ready.map forgetRow = data := by
  induction data generalizing ready with
  | nil =>
    cases ready <;> simp [buildRows]
  | cons a rest ih =>
    constructor
    · intro result
      obtain ⟨b,bs,first,tail,rfl⟩ := two_success (buildRow a) (buildRows rest) List.cons ready result
      rw [List.map_cons,(row_exact a b).mp first,(ih bs).mp tail]
    · intro exactRows
      cases ready with
      | nil => cases exactRows
      | cons b bs =>
        have aligned := List.cons.inj exactRows
        rw [buildRows,(row_exact a b).mpr aligned.1,(ih bs).mpr aligned.2]
        rfl

end Yulang.GeneralSourceMetadataBareRole291
