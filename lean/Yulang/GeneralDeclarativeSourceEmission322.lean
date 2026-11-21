import Yulang.GeneralDeclarativeExistingClause322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceEmission322
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralSourceState (Output)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarationDemands (outputTarget)
open CommonRoleOutermostResolver (All₂)

structure Names where
  input : Nat → Capture
  output : Nat → Nat

def Names.old (names : Names) : GeneralDeclarationDemands.Capture :=
  ⟨fun n => ((names.input n).lower,(names.input n).upper),names.output⟩

def useArg (names : Names) (givenName : Capture) (pattern : Pattern) : Capture :=
  match normalize pattern with
  | .var binder => names.input binder
  | _ => givenName

def useOutput (decl : Declaration) (names : Names) (otherwise : Nat → Nat)
    (eqn : GeneralDeclarations.Equation) : Output :=
  ⟨eqn.name,outputTarget decl names.old otherwise eqn⟩

def inputs (names : Names) (otherwise : Nat → Capture) (position : Nat) : List Pattern → List Capture
  | [] => []
  | p::ps => useArg names (otherwise position) p :: inputs names otherwise (position+1) ps

def demand (decl : Declaration) (clause : Clause) (names : Names) (compound : Nat → Capture)
    (targets : Nat → Nat) : Demand :=
  ⟨clause.role,inputs names compound 0 clause.arguments,clause.outputs.map (useOutput decl names targets)⟩

theorem source_var (names : Names) (elsewhere : Capture)
    (p : Pattern) (observed : normalize p = .var binder) :
    useArg names elsewhere p = names.input binder := by simp [useArg,observed]

theorem erasable (names : Names) (fallback : Capture) (p : Pattern) :
    ((useArg names fallback p).lower,(useArg names fallback p).upper) =
      GeneralDeclarationDemands.inputInterval names.old (fallback.lower,fallback.upper) p := by
  cases h : normalize p <;> simp [useArg,GeneralDeclarationDemands.inputInterval,Names.old,h]

theorem exact_at (names : Names) (compound : Nat → Capture) (first : Nat) (ps : List Pattern)
    (i : Nat) (one : ps[i]? = some p) :
    (inputs names compound first ps)[i]? = some (useArg names (compound (first+i)) p) := by
  induction ps generalizing first i with
  | nil => cases one
  | cons h ps ih =>
    cases i with
    | zero =>
      have eq : h = p := by simpa using one
      subst p
      rfl
    | succ i =>
      have item : ps[i]? = some p := by simpa using one
      change (inputs names compound (first+1) ps)[i]? = some (useArg names (compound (first+(i+1))) p)
      have exactPos : first + 1 + i = first + (i+1) := by omega
      rw [← exactPos]
      exact ih (first+1) i item

theorem outputs_match_source {roles : Roles.RoleDecls} (decl : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (names : Names) (compound : Nat → Capture) (targets : Nat → Nat) :
    (demand decl clause names compound targets).outputs =
      (GeneralDeclarationDemands.childDemand decl clause valid names.old
        ⟨fun i => ((compound i.val).lower,(compound i.val).upper),targets⟩).outputs :=
  rfl

theorem inputs_match_source {roles : Roles.RoleDecls} (decl : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (names : Names) (compound : Nat → Capture) (targets : Nat → Nat)
    (i : Fin (roles clause.role).arity) :
    ∃ arg, (demand decl clause names compound targets).arguments[i.val]? = some arg ∧
      (arg.lower,arg.upper) =
        (GeneralDeclarationDemands.childDemand decl clause valid names.old
           ⟨fun j => ((compound j.val).lower,(compound j.val).upper),targets⟩).arguments i := by
  have within : i.val < clause.arguments.length := by rw [valid.1]; exact i.isLt
  let pat := clause.arguments[i.val]'within
  refine ⟨useArg names (compound (0+i.val)) pat,exact_at names compound 0 clause.arguments i.val
    (List.getElem?_eq_getElem within),?_⟩
  change ((useArg names (compound (0+i.val)) pat).lower,(useArg names (compound (0+i.val)) pat).upper) =
    GeneralDeclarationDemands.inputInterval names.old ((compound i.val).lower,(compound i.val).upper) pat
  rw [Nat.zero_add]
  exact erasable names (compound i.val) pat

end Yulang.GeneralDeclarativeSourceEmission322
