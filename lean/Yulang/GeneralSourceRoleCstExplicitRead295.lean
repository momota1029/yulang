import Yulang.GeneralSourceRoleCstRowExtent295

/-! A read of an explicit implementation body must not be attributed to
the selected declaration's default source. -/
namespace Yulang.GeneralSourceRoleCstExplicitRead295
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles

theorem selected_explicit_preserved {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (arity : Nat)
    (table : RoleSource) (_ : compile policy scope w brand a sealed env arity = some table)
    (impls : AssocEnv) (wf : WellFormed impls.cores) (goal : Goal) (name : Nat)
    (done : resolve impls.cores wf goal = .resolved) (impl : AssocImpl)
    (member : impl ∈ impls.impls) (unique : candidates impls.cores goal = [impl.impl])
    (rhs : Term) (explicit : impl.assoc.lookup name = some rhs) :
    assocOf impls (roleTable table) wf goal name =
      some (rhs.subst (matchingSubst impl.impl.head goal.args)) :=
  GeneralSourceRoleResolverUse292.selected_explicit_independent
    table impls wf goal name done impl member unique rhs explicit

open GeneralSourceRoleCstSelectedControl295 (first packet both naming selected_controls actualRead)
open GeneralSourceRoleResolverFixture292
  (parameterTable explicit_overrides_shell_default role_parameter_used_by_actual_reader)
open Roles.Examples (int str)
open Roles.AssocExamples (char index singletonEnv strImpl str_paterson)

theorem default_and_explicit_reads_differ :
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind actualRead) = some int ∧
    ((compile .selectedBranch 5 both 71 first (packet first) naming 2).bind fun table =>
      assocOf (singletonEnv strImpl) (roleTable table) str_paterson (index str int) 0) = some char := by
  rw [selected_controls.1]
  exact ⟨role_parameter_used_by_actual_reader,explicit_overrides_shell_default⟩

end Yulang.GeneralSourceRoleCstExplicitRead295
