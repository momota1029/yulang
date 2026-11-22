import Yulang.GeneralDeclarativeWitnessProblem349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSignature349
open GeneralDeclarations
open GeneralSourceMetadataRoles291 (RoleSource roleTable index RoleRow fallback)
open GeneralSourceMetadataFiniteLookup291 (get some_sound)
open GeneralSourceMetadataBundle291 (SourceBundle registry)

def declaredEq (roles : Roles.RoleDecls) (role : Nat) (eq : Equation) : Bool :=
  ((roles role).assoc eq.name).isSome

theorem declared_eq (roles : Roles.RoleDecls) (role : Nat) (eq : Equation) :
    declaredEq roles role eq = true ↔ GeneralDeclarations.Declared roles role eq := by
  unfold declaredEq GeneralDeclarations.Declared
  cases h : (roles role).assoc eq.name <;> simp

def checksClause (roles : Roles.RoleDecls) (clause : Clause) : Bool :=
  decide (clause.arguments.length = (roles clause.role).arity) &&
    clause.outputs.all (declaredEq roles clause.role)

theorem clause_of_check {roles : Roles.RoleDecls} {clause : Clause}
    (found : checksClause roles clause = true) : clause.Signature roles := by
  obtain ⟨arity,outs⟩ := GeneralDeclarativeWitnessProblem349.splitAnd found
  exact ⟨of_decide_eq_true arity,fun _ h => (declared_eq ..).mp (List.all_eq_true.mp outs _ h)⟩

def checkedEntry (d : Declaration) (e : Nat × Option Roles.Term) : Bool :=
  e.2.isSome || decide (e.1 ∈ d.associated.map Equation.name)

def covers (roles : RoleSource) (d : Declaration) : Bool :=
  match get d.role (index roles) with
  | none => true
  | some row => row.outputs.all (checkedEntry d)

theorem covers_required {roles : RoleSource} {d : Declaration} (ok : covers roles d = true)
    (name : Nat) (body : Option Roles.Term) (listed : (roleTable roles d.role).assoc name = some body) :
    (∃ e ∈ d.associated, e.name = name) ∨ body.isSome = true := by
  unfold covers at ok
  unfold roleTable at listed
  cases ix : get d.role (index roles) with
  | none =>
    rw [ix] at listed
    cases listed
  | some row =>
    rw [ix] at ok listed
    have fromRow : get name row.outputs = some body := listed
    have entry := List.all_eq_true.mp ok (name,body) (some_sound fromRow)
    rcases GeneralDeclarativeWitnessProblem349.splitOr entry with yes|yes
    · exact .inr yes
    · exact .inl (List.mem_map.mp (of_decide_eq_true yes))

def checks (roles : RoleSource) (d : Declaration) : Bool :=
  (decide (d.head.length = (roleTable roles d.role).arity) &&
    d.associated.all (declaredEq (roleTable roles) d.role)) &&
  (covers roles d && d.requirements.all (checksClause (roleTable roles)))

theorem checked_signature {roles : RoleSource} {d : Declaration} (ok : checks roles d = true) :
    d.Signature (roleTable roles) := by
  obtain ⟨first,last⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
  obtain ⟨arity,rows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd first
  obtain ⟨allReq,child⟩ := GeneralDeclarativeWitnessProblem349.splitAnd last
  exact ⟨of_decide_eq_true arity,fun _ h => (declared_eq ..).mp (List.all_eq_true.mp rows _ h),
    covers_required allReq,fun _ h => clause_of_check (List.all_eq_true.mp child _ h)⟩

end Yulang.GeneralDeclarativeWitnessSignature349
