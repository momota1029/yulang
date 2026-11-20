import Yulang.GeneralSourceRoleExport292

/-! Closed symbolic mirror of a flat role with required and default outputs.
This intentionally fixes the spelling input while varying resolver identities. -/
namespace Yulang.GeneralSourceRoleFixture292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

def indexRole : Role :=
  ⟨"Index",["'container","'key"],
    [⟨"value",.required⟩,⟨"fallback",.binder "'key"⟩,⟨"scalar",.nullary "char"⟩]⟩

def fixtureEnv (offset : Nat) : Environment :=
  ⟨fun s => if s = "Index" then some (offset+1) else none,
   fun role name => if role ≠ offset+1 then none else
     if name = "value" then some (offset+2) else
     if name = "fallback" then some (offset+3) else
     if name = "scalar" then some (offset+4) else none,
   fun n => if n = "char" then some (offset+5) else none⟩

def projected (offset : Nat) : Option (Nat × List (Option (Option Roles.Term))) :=
  (lower (fixtureEnv offset) 0 [indexRole]).map fun table =>
    let role := roleTable table (offset+1)
    (offset+1,[role.assoc (offset+2),role.assoc (offset+3),
      role.assoc (offset+4),role.assoc (offset+6)])

theorem exact_worlds :
    projected 0 = some (1,[some none,some (some (.var 1)),some (some (.app 5 [])),none]) ∧
    projected 7 = some (8,[some none,some (some (.var 1)),some (some (.app 12 [])),none]) := by decide

/-- Source spelling alone need not determine the identity in all admissible
resolver inputs. This is about a missing input, not a requirement to use one
particular compiler numbering scheme. -/
theorem no_universal_source_role_id :
    ¬ ∃ f : Role → Nat, ∀ offset r,
      (fixtureEnv offset).role r.spelling = some (f r) := by
  rintro ⟨f,agree⟩
  have h₀ := agree 0 indexRole
  have h₇ := agree 7 indexRole
  change some 1 = some (f indexRole) at h₀
  change some 8 = some (f indexRole) at h₇
  have bad : (1 : Nat) = 8 := Option.some.inj (h₀.trans h₇.symm)
  cases bad

def duplicateBinder : Role := {indexRole with binders := ["'key","'key"]}
def missingBinder : Role := {indexRole with binders := ["'container"]}

theorem malformed_inputs :
    (lower (fixtureEnv 0) 0 [duplicateBinder]).isNone = true ∧
    (lower (fixtureEnv 0) 0 [missingBinder]).isNone = true ∧
    (lower (fixtureEnv 0) 0 [indexRole,indexRole]).isNone = true := by decide

#guard (projected 0).isSome
#guard (projected 7).isSome

end Yulang.GeneralSourceRoleFixture292
