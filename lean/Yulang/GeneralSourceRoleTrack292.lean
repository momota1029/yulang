import Yulang.GeneralSourceRoleHeadPacketRun292

/-! Carry independent occurrence handles without using them as numeric roles,
positions or type constructor keys. Exactness is for the supplied occurrences. -/
namespace Yulang.GeneralSourceRoleTrack292
open GeneralSourceRoleHeadPacketRun292 (Source Origin run assoc_exact)
open GeneralSourceRoleHeadShape292 (Head HeadShape)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleSyntaxBoundary292 (Admitted Owner)
open GeneralSourceRoleSpelling292 (Environment Output ResolvedBody)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)

structure Tracked (Scope Handle : Type) where
  scope : Scope
  head : Head
  atRole : Handle
  body : List (Handle × Child)

def forget {Scope Handle : Type} (entry : Tracked Scope Handle) : Source Scope :=
  ⟨entry.scope,entry.head,entry.body.map Prod.snd⟩

def runTracked {Scope Handle : Type} (env : Scope → Environment) (fallback : Nat)
    (src : List (Tracked Scope Handle)) : Option RoleSource :=
  run env fallback (src.map forget)

def OriginAt {Scope Handle : Type} (env : Scope → Environment) (src : List (Tracked Scope Handle))
    (r n : Nat) (term : Option Roles.Term) (roleSite typeSite : Handle) : Prop :=
  ∃ entry ∈ src, entry.atRole = roleSite ∧ ∃ name params,
    HeadShape entry.head name params ∧ (env entry.scope).role name = some r ∧
      ∃ child, (typeSite, Child.typeDecl child) ∈ entry.body ∧
        ∃ o : Output, Admitted .roleBodyDirect child o ∧
          (env entry.scope).output r o.spelling = some n ∧
          ResolvedBody (env entry.scope) params o.body term

theorem origin_exact {Scope Handle : Type} (env : Scope → Environment) (src : List (Tracked Scope Handle))
    (r n : Nat) (term : Option Roles.Term) :
    Origin env (src.map forget) r n term ↔ ∃ rSite tSite, OriginAt env src r n term rSite tSite := by
  constructor
  · rintro ⟨base,inInput,name,params,ordered,roleKey,child,inBody,o,admitted,outID,bodyOK⟩
    obtain ⟨original,originalIn,rfl⟩ := List.mem_map.mp inInput
    obtain ⟨item,originalChild,e⟩ := List.mem_map.mp inBody
    rcases item with ⟨site,label⟩
    change label = Child.typeDecl child at e
    subst label
    exact ⟨original.atRole,site,original,originalIn,rfl,name,params,ordered,roleKey,child,
      originalChild,o,admitted,outID,bodyOK⟩
  · rintro ⟨_,tSite,original,originalIn,_,name,params,ordered,roleKey,child,inBody,
      o,admitted,outID,bodyOK⟩
    exact ⟨forget original,List.mem_map.mpr ⟨original,originalIn,rfl⟩,name,params,ordered,
      roleKey,child,List.mem_map.mpr ⟨(tSite,.typeDecl child),inBody,rfl⟩,o,admitted,outID,bodyOK⟩

theorem tracked_readback_exact {Scope Handle : Type}
    (env : Scope → Environment) (fallback : Nat) (src : List (Tracked Scope Handle))
    (out : RoleSource) (success : runTracked env fallback src = some out)
    (r n : Nat) (term : Option Roles.Term) :
    (roleTable out r).assoc n = some term ↔ ∃ rSite tSite, OriginAt env src r n term rSite tSite :=
  (assoc_exact env fallback (src.map forget) out success r n term).trans (origin_exact ..)

end Yulang.GeneralSourceRoleTrack292
