import Yulang.GeneralSourceRoleCstSelectedExtent295

/-! A successful table observation retains a source interval inside the
one selected role. Optional payloads still distinguish required defaults. -/
namespace Yulang.GeneralSourceRoleCstRowExtent295
open GeneralSourceRoleCstWire293 (Wire Transfer spelling)
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstSpan293 (Extent locate)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile compile_origin)
open GeneralSourceRoleCstSelectedReadback295 (AnchoredAssoc exact_for_entry)
open GeneralSourceRoleCstSelectedExtent295 (selected_member_contained)
open GeneralSourceRoleCstWirePaths293 (atWire)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstTypeRules293 (IsType type_exact)
open GeneralSourceRoleTrack292 (Tracked OriginAt)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleSyntaxBoundary292 (Shape)

theorem read_locates_own_type {S B : Type} [DecidableEq B] [DecidableEq S]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (built : compile policy scope w brand a sealed env fallback = some table)
    (role name : Nat) (term : Option Roles.Term) (found : (roleTable table role).assoc name = some term) :
    ∃ (p : Tracked S (Address B)) (site : Address B) (shape : Shape)
      (root selected t : Tree) (raw : Wire) (outer inner : Extent),
      OriginAt env [p] role name term a site ∧ Transfer w root ∧
      locate a.path root 0 = some (selected,outer) ∧ locate site.path root 0 = some (t,inner) ∧
      atWire site.path w = some raw ∧ Transfer raw t ∧ IsType t shape ∧
      outer.low ≤ inner.low ∧ inner.high ≤ outer.high ∧
      inner.high = inner.low + (spelling raw).utf8ByteSize := by
  obtain ⟨_,_,p,roleSite,produced,attached⟩ :=
    compile_origin policy scope w brand a sealed env fallback table built
  obtain ⟨site,shape,_,_,_,_,_,source,member,_⟩ :=
    (exact_for_entry policy scope w brand a sealed.selected env fallback p table produced roleSite
      attached role name term).mp found
  obtain ⟨root,selected,t,raw,outer,inner,map,selectedAt,siteAt,wireAt,transfer,classified,lo,hi,sz⟩ :=
    selected_member_contained policy scope w brand a sealed.selected p produced (site,.typeDecl shape) member
  cases classified with
  | associated cs sh valid =>
    exact ⟨p,site,shape,root,selected,_,raw,outer,inner,source,map,selectedAt,siteAt,wireAt,transfer,
      (type_exact ..).mp valid,lo,hi,sz⟩

end Yulang.GeneralSourceRoleCstRowExtent295
