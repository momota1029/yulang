import Yulang.GeneralSourceRoleCstSelectedMembers295

namespace Yulang.GeneralSourceRoleCstSelectedReadback295
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile compile_origin)
open GeneralSourceRoleCstSelectedMembers295 (selected_member_is_exact_original)
open GeneralSourceRoleCstWirePaths293 (atWire)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleTrack292 (Tracked OriginAt runTracked tracked_readback_exact)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

def AnchoredAssoc {Scope Brand : Type} (w : Wire) (env : Scope → Environment)
    (entry : Tracked Scope (Address Brand)) (selected : Address Brand)
    (role name : Nat) (term : Option Roles.Term) : Prop :=
  ∃ site shape raw tree b st leaf,
    OriginAt env [entry] role name term selected site ∧
      ((site,Child.typeDecl shape) ∈ entry.body) ∧
      site.brand = selected.brand ∧ site.path = selected.path ++ [b,st,leaf] ∧
      atWire site.path w = some raw ∧ Transfer raw tree ∧ Classification tree (.typeDecl shape)

theorem exact_for_entry {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Selection Brand) (env : Scope → Environment) (fallback : Nat)
    (p : Tracked Scope (Address Brand)) (table : RoleSource)
    (produced : select policy scope w brand a sealed = some p)
    (roleSite : p.atRole = a) (attached : runTracked env fallback [p] = some table)
    (role name : Nat) (term : Option Roles.Term) :
    (roleTable table role).assoc name = some term ↔ AnchoredAssoc w env p a role name term := by
  rw [tracked_readback_exact env fallback [p] table attached role name term]
  constructor
  · rintro ⟨source,site,fromHere⟩
    rcases fromHere with ⟨entry,single,siteID,n,ps,hh,mapped,sh,inBody,o,shape,oo,resolved⟩
    have belong := List.mem_singleton.mp single
    subst entry
    have present := selected_member_is_exact_original policy scope w brand a sealed p produced
      (site,.typeDecl sh) inBody
    obtain ⟨same,⟨b,st,leaf,suffix⟩,t,raw,found,conversion,classed⟩ := present
    exact ⟨site,sh,raw,t,b,st,leaf,⟨p,by simp,roleSite,n,ps,hh,mapped,sh,inBody,o,shape,oo,resolved⟩,
      inBody,same,suffix,found,conversion,classed⟩
  · rintro ⟨site,sh,raw,tree,b,st,leaf,origin,_⟩
    exact ⟨a,site,origin⟩

theorem anchor_declaration {Scope Brand : Type} [DecidableEq Scope] [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (sealed : Boundary Scope Brand) (env : Scope → Environment) (fallback : Nat)
    (table : RoleSource) (ok : compile policy scope w brand a sealed env fallback = some table)
    (role name : Nat) (term : Option Roles.Term) :
    ∃ p, p.atRole = a ∧ a = sealed.selected.address ∧
     ((roleTable table role).assoc name = some term ↔ AnchoredAssoc w env p a role name term) := by
  obtain ⟨_,eq,p,site,produced,attached⟩ := compile_origin policy scope w brand a sealed env fallback table ok
  exact ⟨p,site,eq,exact_for_entry policy scope w brand a sealed.selected env fallback p table produced site
    attached role name term⟩

end Yulang.GeneralSourceRoleCstSelectedReadback295
