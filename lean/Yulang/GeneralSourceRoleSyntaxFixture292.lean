import Yulang.GeneralSourceRoleSyntaxPipeline292

/-! Closed synthetic shell matching the supported shapes. These checks do not
execute the Rust parser. A partial shell can pass but loses a default; this
explains why a parser producer must prove completeness, not only provenance. -/
namespace Yulang.GeneralSourceRoleSyntaxFixture292
open GeneralSourceRoleSpelling292 GeneralSourceRoleSyntaxBoundary292 GeneralSourceRoleSyntaxPipeline292
open GeneralSourceRoleFixture292 (indexRole fixtureEnv projected)
open GeneralSourceMetadataRoles291 (roleTable)

def requiredValue : Shape := ⟨"value",false,.absent,true⟩
def binderDefault : Shape := ⟨"fallback",true,.binder "'key",true⟩
def charDefault : Shape := ⟨"scalar",true,.nullary "char",true⟩
def full : Shell := ⟨"Index",["'container","'key"],[requiredValue,binderDefault,charDefault]⟩
def missing : Shell := {full with directTypeChildren := [requiredValue,charDefault]}
def broken : Shell :=
  {full with directTypeChildren := [requiredValue,⟨"fallback",true,.recovery,false⟩,charDefault]}
def reversed : Shell := {full with parameters := full.parameters.reverse}

def read (env : Environment) (shell : Shell) (role name : Nat) :
    Option (Option (Option Roles.Term)) :=
  (applyShells env 0 [shell]).map fun out => (roleTable out role).assoc name

theorem same_symbolic : projectRole full = some indexRole := by decide

theorem exact_readback :
    read (fixtureEnv 0) full 1 2 = some (some none) ∧
    read (fixtureEnv 0) full 1 3 = some (some (some (.var 1))) ∧
    read (fixtureEnv 0) full 1 4 = some (some (some (.app 5 []))) ∧
    read (fixtureEnv 0) full 1 6 = some none := by decide

theorem incomplete_shell_loses_default :
    read (fixtureEnv 0) missing 1 2 = some (some none) ∧
    read (fixtureEnv 0) missing 1 3 = some none ∧
    read (fixtureEnv 0) missing 1 4 = some (some (some (.app 5 []))) := by decide

theorem broken_shell_rejected : (applyShells (fixtureEnv 0) 0 [broken]).isNone = true := by decide

theorem binder_order_observed :
    read (fixtureEnv 0) full 1 3 = some (some (some (.var 1))) ∧
    read (fixtureEnv 0) reversed 1 3 = some (some (some (.var 0))) := by decide

theorem exact_same_shell_two_accepted_worlds :
    read (fixtureEnv 0) full 1 4 = some (some (some (.app 5 []))) ∧
    read (fixtureEnv 7) full 8 11 = some (some (some (.app 12 []))) ∧
    read (fixtureEnv 7) full 1 4 = some none := by decide

/-- Arbitrary extra numbering hypotheses cannot remove this difference while
both of these already accepted worlds remain in scope. -/
theorem no_environment_free_table :
    ¬ ∃ f : Shell → Nat → Nat → Option (Option (Option Roles.Term)),
        ∀ (offset : Nat) (s : Shell) (r n : Nat), f s r n = read (fixtureEnv offset) s r n := by
  rintro ⟨func,uniform⟩
  have bad := (uniform 0 full 1 4).symm.trans (uniform 7 full 1 4)
  rw [exact_same_shell_two_accepted_worlds.1,exact_same_shell_two_accepted_worlds.2.2] at bad
  cases bad

#guard (applyShells (fixtureEnv 0) 0 [full]).isSome
#guard (applyShells (fixtureEnv 0) 0 [missing]).isSome
#guard (applyShells (fixtureEnv 0) 0 [broken]).isNone

end Yulang.GeneralSourceRoleSyntaxFixture292
