import Yulang.GeneralSourceRoleScopedRead292

/-! Two source sites may have equal short spellings while the external
scope environments attest different numeric roles. The language's scope
resolution is intentionally not part of this example. -/
namespace Yulang.GeneralSourceRoleScopedFixture292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleScopedExport292 (ScopedRole lower)
open GeneralSourceRoleScopedRead292 (SourceAssoc site_exact)
open GeneralSourceRoleFixture292 (indexRole fixtureEnv)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

def scopedInputs : List (ScopedRole Bool) := [⟨false,indexRole⟩,⟨true,indexRole⟩]
def scopeEnv (site : Bool) : Environment := fixtureEnv (if site then 7 else 0)

def values : Option (List (Option (Option Roles.Term))) :=
  (lower scopeEnv 0 scopedInputs).map fun out =>
    [(roleTable out 1).assoc 4,(roleTable out 8).assoc 11,(roleTable out 1).assoc 11]

theorem same_short_names_distinct_scoped_values :
    values = some [some (some (.app 5 [])),some (some (.app 12 [])),none] := by decide

theorem same_semantic_id_rejected :
    (lower (fun _ => fixtureEnv 0) 0 scopedInputs).isNone = true := by decide

theorem positive_source_scope :
    ∀ out, lower scopeEnv 0 scopedInputs = some out →
      SourceAssoc scopeEnv scopedInputs 8 11 (some (.app 12 [])) ∧
      (roleTable out 8).assoc 11 = some (some (.app 12 [])) := by
  intro out h
  have site : SourceAssoc scopeEnv scopedInputs 8 11 (some (.app 12 [])) := by
    refine ⟨⟨true,indexRole⟩,by simp [scopedInputs],rfl,⟨"scalar",.nullary "char"⟩,?_,rfl,?_⟩
    · decide
    · exact .nullary rfl
  exact ⟨site,(site_exact h 8 11 _).mpr site⟩

#guard values.isSome
#guard (lower (fun _ => fixtureEnv 0) 0 scopedInputs).isNone

end Yulang.GeneralSourceRoleScopedFixture292
