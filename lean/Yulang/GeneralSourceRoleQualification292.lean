import Yulang.GeneralSourceRoleEnvExact292
import Yulang.GeneralSourceRoleDiagnosticFixture292

/-! The flat adapter is intentionally a single-spelling namespace. It cannot
supply distinct identities for distinct qualified sites with the same spelling.
No claim is made that the current source language accepts a particular
shadowing or multi-module program. -/
namespace Yulang.GeneralSourceRoleQualification292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292
open GeneralSourceMetadataRoles291 (RoleSource RoleRow)
open GeneralSourceMetadataBareRole291 (forgetRow)

theorem same_spelling_same_key {env : Environment} {a b : Role}
    {x y : GeneralSourceMetadataBareRole291.BareRow}
    (same : a.spelling = b.spelling)
    (first : RowWitness env a x) (second : RowWitness env b y) : x.role = y.role := by
  apply Option.some.inj
  calc
    some x.role = env.role a.spelling := first.2.1.symm
    _ = env.role b.spelling := congrArg env.role same
    _ = some y.role := second.2.1

theorem leading_same_spelling_not_accepted (env : Environment) (fallback : Nat)
    (a b : Role) (tail : List Role) (same : a.spelling = b.spelling)
    (out : RoleSource) : lower env fallback (a :: b :: tail) ≠ some out := by
  intro success
  obtain ⟨_,shape,valid⟩ := (lower_exact ..).mp success
  rcases out with ⟨arity,rows⟩
  cases rows with
  | nil => cases shape
  | cons first rest =>
    cases rest with
    | nil =>
      have inv := shape
      cases inv with
      | cons h t => cases t
    | cons second rows =>
      change Aligned (RowWitness env) (a :: b :: tail)
        (forgetRow first :: forgetRow second :: rows.map forgetRow) at shape
      cases shape with
      | cons wa remaining =>
        cases remaining with
        | cons wb _ =>
          have equal := same_spelling_same_key same wa wb
          change first.role = second.role at equal
          have nondup := valid.1
          change (first.role :: second.role :: rows.map RoleRow.role).Nodup at nondup
          exact (List.nodup_cons.mp nondup).1 (by rw [equal]; exact List.mem_cons_self)

end Yulang.GeneralSourceRoleQualification292

namespace Yulang.GeneralSourceRoleQualification292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (Shell)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceMetadataRoles291 (roleTable)

def twoRoles : List Shell :=
  [⟨"A",[],[⟨"value",false,.absent,true⟩]⟩,
   ⟨"B",[],[⟨"value",true,.nullary "char",true⟩]⟩]

def localNameEnvironment : Environment :=
  ⟨fun name => if name = "A" then some 10 else if name = "B" then some 11 else none,
   fun role name => if (role = 10 ∨ role = 11) ∧ name = "value" then some 2 else none,
   fun name => if name = "char" then some 12 else none⟩

theorem output_identity_is_role_local :
    ((applyShells localNameEnvironment 0 twoRoles).map fun table =>
      [(roleTable table 10).assoc 2,(roleTable table 11).assoc 2]) =
      some [some none,some (some (.app 12 []))] := by decide

/-- Two independently witnessed semantic IDs cannot be constructed from one
shared spelling by a flat lookup; the necessary namespace evidence is absent. -/
theorem no_flat_resolver_for_distinct_qualified_roles (e : Environment)
    (left right : String) (equal : left = right) (l r : Nat) (different : l ≠ r) :
    ¬ (e.role left = some l ∧ e.role right = some r) := by
  rintro ⟨a,b⟩
  subst right
  exact different (Option.some.inj (a.symm.trans b))

end Yulang.GeneralSourceRoleQualification292
