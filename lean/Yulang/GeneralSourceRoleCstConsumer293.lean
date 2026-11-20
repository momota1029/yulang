import Yulang.GeneralSourceRoleCstSnapshot293

/-! Functional composition with the old role table, conditional on the
explicitly supplied and separately checked name-resolution environment. -/
namespace Yulang.GeneralSourceRoleCstConsumer293
open GeneralSourceRoleCstSnapshot293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleTrack292 (Tracked runTracked tracked_readback_exact)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleSyntaxBoundary292 (Shape Admitted Owner)

theorem assoc_locates_type {Scope Brand : Type} [DecidableEq Brand]
    (s : Snapshot Brand) (a : Address Brand) (scope : Scope)
    (payload : Tracked Scope (Address Brand)) (produced : exportAt scope s a = some payload)
    (env : Scope → Environment) (fallback : Nat) (table : RoleSource)
    (attached : runTracked env fallback [payload] = some table)
    (roleID nameID : Nat) (value : Option Roles.Term)
    (read : (roleTable table roleID).assoc nameID = some value) :
    ∃ typeSite tree shape,
      (typeSite,.typeDecl shape) ∈ payload.body ∧
      atAddress s typeSite = some tree ∧ Classification tree (.typeDecl shape) := by
  obtain ⟨roleSite,typeSite,entry,inPayload,entrySite,n,params,ordinary,k,
    sh,inBody,member,wellShaped,resolvedName,resolvedBody⟩ :=
    (tracked_readback_exact env fallback [payload] table attached roleID nameID value).mp read
  have o := List.mem_singleton.mp inPayload
  subst entry
  obtain ⟨raw,located,kind⟩ :=
    declaration_member_roundtrip scope s a payload produced (typeSite,.typeDecl sh) inBody
  exact ⟨typeSite,raw,sh,inBody,located,kind⟩

end Yulang.GeneralSourceRoleCstConsumer293
