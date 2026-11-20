import Yulang.GeneralSourceRoleChildCoverage292
import Yulang.GeneralSourceRoleSyntaxFixture292

/-! A checked hand-off for a *supplied* complete direct-child inventory.
Keeping the source inventory as separate input makes accidental omissions
detectable without pretending to reconstruct that inventory from a shell. -/
namespace Yulang.GeneralSourceRoleCoveredShell292
open GeneralSourceRoleChildCoverage292
open GeneralSourceRoleSyntaxBoundary292 (Shell Shape)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleExport292 (collect Aligned collect_exact)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure Inventory where
  name : String
  parameters : List String
  directChildren : List Child

def Checked (source : Inventory) (shell : Shell) : Prop :=
  source.name = shell.name ∧ source.parameters = shell.parameters ∧
  Collects source.directChildren shell.directTypeChildren

def prepare (s : Inventory) : Option Shell :=
  (scan s.directChildren).map fun children => ⟨s.name,s.parameters,children⟩

theorem prepare_exact (source : Inventory) (shell : Shell) :
    prepare source = some shell ↔ Checked source shell := by
  rcases shell with ⟨n,params,types⟩
  unfold prepare Checked
  rw [←scan_exact]
  cases h : scan source.directChildren <;> simp [Shell.mk.injEq]

def verify (s : Inventory) (out : Shell) : Bool :=
  decide (s.name = out.name) && decide (s.parameters = out.parameters) &&
    decide (scan s.directChildren = some out.directTypeChildren)

theorem verify_exact (source : Inventory) (shell : Shell) :
    verify source shell = true ↔ Checked source shell := by
  simp [verify,Checked,Bool.and_eq_true,scan_exact,and_assoc]

def run (env : Environment) (arity : Nat) (sources : List Inventory) : Option RoleSource :=
  (collect prepare sources).bind (applyShells env arity)

theorem run_exact (env : Environment) (arity : Nat) (sources : List Inventory) (out : RoleSource) :
    run env arity sources = some out ↔ ∃ shells, Aligned Checked sources shells ∧
      applyShells env arity shells = some out := by
  constructor
  · intro h
    obtain ⟨shells,extracted,result⟩ := bind_success h
    exact ⟨shells,(collect_exact _ _ prepare_exact _ _).mp extracted,result⟩
  · rintro ⟨shells,extracted,result⟩
    unfold run
    rw [(collect_exact _ _ prepare_exact _ _).mpr extracted]
    exact result

theorem every_direct_type {source : Inventory} {shell : Shell}
    (ok : verify source shell = true) (node : Shape) :
    node ∈ shell.directTypeChildren ↔ Child.typeDecl node ∈ source.directChildren :=
  member_exact ((verify_exact ..).mp ok).2.2 node

open GeneralSourceRoleSyntaxFixture292 (requiredValue binderDefault charDefault full missing)
open GeneralSourceRoleFixture292 (fixtureEnv)

def packet : Inventory :=
  ⟨full.name,full.parameters,[.typeDecl requiredValue,.other,.typeDecl binderDefault,.typeDecl charDefault]⟩

def corrupted : Inventory :=
  {packet with directChildren := [.typeDecl requiredValue,.unknown,.typeDecl charDefault]}

theorem observable_controls :
    verify packet full = true ∧ verify packet missing = false ∧
    (prepare corrupted).isNone = true := by decide

theorem exact_checked_inventory_has_default :
    ((run (fixtureEnv 0) 0 [packet]).map (fun table => (roleTable table 1).assoc 3)) =
      some (some (some (.var 1))) := by decide

#guard verify packet full
#guard !(verify packet missing)

end Yulang.GeneralSourceRoleCoveredShell292
