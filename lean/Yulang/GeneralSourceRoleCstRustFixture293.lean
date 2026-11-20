import Yulang.GeneralSourceRoleCstRustOrigin293

/-! Current role-head wrapper control with a separately supplied old name
map. The golden replay is tested by the external JSON executable. -/
namespace Yulang.GeneralSourceRoleCstRustFixture293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstFixture293 (ws id sigil role block namedBody method)
open GeneralSourceRoleCstRustRole293 (extract extract_exact)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleCstSnapshot293 (Address Snapshot mark)
open GeneralSourceRoleCstFixture293 (result)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleResolverFixture292 (localEnv parameterTable role_parameter_used_by_actual_reader)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles
open Roles.Examples (int str)
open Roles.AssocExamples (index singletonEnv omittedImpl omitted_paterson)

def actualHead : Tree := .node .head
  [id "Index",.node .argument [ws,.node .head [sigil "'container"]],
    .node .argument [ws,.node .head [sigil "'key"]]]

def actualRole : Tree := role actualHead (block (namedBody (sigil "'key")) method)
def wrapped : Snapshot Nat := ⟨10,.node .root [actualRole]⟩

def expected : Tracked Unit (Address Nat) :=
  mark 10 ⟨(),GeneralSourceRoleCstShapes293.toHead "Index" ["'container","'key"],[0],
    [([0,6,1,0],.typeDecl ⟨"value",true,.binder "'key",true⟩),([0,6,3,0],.other)]⟩

theorem wrapped_roles_export : exportAt () wrapped ⟨10,[0]⟩ = some expected := rfl

theorem previously_shallow_role_rejected :
    extract () [] (role GeneralSourceRoleCstFixture293.head
      (block (namedBody (sigil "'key")) method)) = none := rfl

theorem wrapped_roles_attach :
    ((exportAt () wrapped ⟨10,[0]⟩).bind fun payload =>
       runTracked (fun _ => localEnv) 2 [payload]) = some parameterTable := rfl

theorem wrapped_roles_actual_consumer :
    ∀ table : RoleSource, ((exportAt () wrapped ⟨10,[0]⟩).bind fun payload =>
       runTracked (fun _ => localEnv) 2 [payload]) = some table →
      assocOf (singletonEnv omittedImpl) (roleTable table) omitted_paterson (index str int) 0 = some int := by
  intro table attached
  have e := Option.some.inj (attached.symm.trans wrapped_roles_attach)
  subst table
  exact role_parameter_used_by_actual_reader

theorem wrapper_paths_unique {Scope : Type} (scope : Scope) (p : List Nat)
    (tree : Tree) (out : Tracked Scope (List Nat)) (accepted : extract scope p tree = some out) :
    (out.body.map Prod.fst).Nodup := by
  obtain ⟨head,j,n,ps,cs,selected,headOK,scopeOK,address,read,items⟩ :=
    (extract_exact ..).mp accepted
  exact GeneralSourceRoleCstDistinct293.aligned_paths_unique (p ++ [j]) cs out.body items

#guard (exportAt () wrapped ⟨10,[0]⟩).isSome

end Yulang.GeneralSourceRoleCstRustFixture293
