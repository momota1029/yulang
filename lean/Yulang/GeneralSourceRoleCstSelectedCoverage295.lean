import Yulang.GeneralSourceRoleCstOutcomePrecise295

/-! If the old exporter succeeds, it has not silently dropped a selected
associated declaration. This is completeness of the scoped handoff only. -/
namespace Yulang.GeneralSourceRoleCstSelectedCoverage295
open GeneralSourceRoleTrack292 (Tracked forget runTracked OriginAt tracked_readback_exact)
open GeneralSourceRoleCstSelectedRow295 (aligned_singleton map_singleton)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile compile_origin)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleSyntaxBoundary292 (Shape Admitted)
open GeneralSourceRoleChildCoverage292 (Child member_exact)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

theorem tracked_type_contributes {S H : Type} (env : S → Environment) (fallback : Nat)
    (p : Tracked S H) (table : RoleSource) (done : runTracked env fallback [p] = some table)
    (site : H) (shape : Shape) (selected : (site,Child.typeDecl shape) ∈ p.body) :
    ∃ role name value, OriginAt env [p] role name value p.atRole site ∧
      (roleTable table role).assoc name = some value := by
  obtain ⟨packets,prepared,built⟩ :=
    (GeneralSourceRoleHeadPacketRun292.run_exact env fallback [forget p] table).mp done
  obtain ⟨packet,rfl,ready⟩ := aligned_singleton prepared
  obtain ⟨entries,projected,result⟩ := (GeneralSourceRoleScopedShell292.run_exact ..).mp built
  obtain ⟨entry,rfl,clear⟩ := aligned_singleton projected
  obtain ⟨stored,rows,validated⟩ := (GeneralSourceRoleScopedExport292.lower_exact ..).mp result
  obtain ⟨bare,one,rowWitness⟩ := aligned_singleton rows
  obtain ⟨r,oneRow,rfl⟩ := map_singleton one
  obtain ⟨scopeEq,direct,head⟩ := ready
  obtain ⟨scopeLink,s,⟨srcName,srcArgs,scan⟩,symbol,params,projections⟩ := clear
  obtain ⟨_,roleKey,_,allOutputs⟩ := rowWitness
  have child : Child.typeDecl shape ∈ packet.source.directChildren := by
    rw [direct]
    exact List.mem_map.mpr ⟨(site,.typeDecl shape),selected,rfl⟩
  have declared := (member_exact scan shape).mpr child
  obtain ⟨out,mapped,admitted⟩ := GeneralSourceRoleManifest292.aligned_left projections declared
  obtain ⟨⟨name,value⟩,field,witness⟩ := GeneralSourceRoleManifest292.aligned_left allOutputs mapped
  obtain ⟨key,lowered⟩ := witness
  change (env entry.scope).role entry.role.spelling = some r.role at roleKey
  change (env entry.scope).output r.role out.spelling = some name at key
  rw [←scopeLink,scopeEq,←symbol,←srcName] at roleKey
  rw [←scopeLink,scopeEq] at key
  rw [←scopeLink,scopeEq,←params,←srcArgs] at lowered
  have origin : OriginAt env [p] r.role name value p.atRole site :=
    ⟨p,List.mem_cons_self,rfl,packet.source.name,packet.source.parameters,
      head,roleKey,shape,selected,out,admitted,key,lowered⟩
  exact ⟨r.role,name,value,origin,
    (tracked_readback_exact env fallback [p] table done r.role name value).mpr ⟨p.atRole,site,origin⟩⟩

theorem selected_type_contributes {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Boundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (ok : compile policy scope w brand a packet env fallback = some table) :
    ∃ p : Tracked S (Address B), p.atRole = a ∧
      GeneralSourceRoleCstSelectedSeal295.select policy scope w brand a packet.selected = some p ∧
      ∀ site shape, (site,Child.typeDecl shape) ∈ p.body →
      ∃ role name value, OriginAt env [p] role name value a site ∧
        (roleTable table role).assoc name = some value := by
  obtain ⟨_,_,p,site,got,done⟩ := compile_origin policy scope w brand a packet env fallback table ok
  refine ⟨p,site,got,?_⟩
  intro origin shape m
  simpa only [site] using tracked_type_contributes env fallback p table done origin shape m

end Yulang.GeneralSourceRoleCstSelectedCoverage295
