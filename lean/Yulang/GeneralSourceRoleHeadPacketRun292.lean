import Yulang.GeneralSourceRoleHeadShape292

/-! Complete composition from an independently supplied scoped head walk and
direct body inventory through to role lookup. Parser evidence remains external. -/
namespace Yulang.GeneralSourceRoleHeadPacketRun292
open GeneralSourceRoleSpelling292 (Environment Output ResolvedBody)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleHeadShape292 (Head HeadShape packet packet_exact)
open GeneralSourceRoleScopedShell292 (Packet)
open GeneralSourceRoleExport292 (Aligned collect collect_exact)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleSyntaxBoundary292 (Admitted Owner)
open GeneralSourceMetadataExprDomain291 (bind_success)
open GeneralSourceRoleManifest292 (aligned_left aligned_right)

structure Source (Scope : Type) where
  scope : Scope
  head : Head
  body : List Child

def makePacket {Scope : Type} (s : Source Scope) : Option (Packet Scope) :=
  packet s.scope s.head s.body

def Represents {Scope : Type} (s : Source Scope) (p : Packet Scope) : Prop :=
  p.scope = s.scope ∧ p.source.directChildren = s.body ∧
    HeadShape s.head p.source.name p.source.parameters

theorem make_exact {Scope : Type} (s : Source Scope) (p : Packet Scope) :
    makePacket s = some p ↔ Represents s p := packet_exact s.scope s.head s.body p

def run {Scope : Type} (env : Scope → Environment) (fallback : Nat) (files : List (Source Scope)) :
    Option RoleSource := (collect makePacket files).bind (GeneralSourceRoleScopedShell292.run env fallback)

theorem run_exact {Scope : Type} (env : Scope → Environment) (fallback : Nat)
    (files : List (Source Scope)) (out : RoleSource) :
    run env fallback files = some out ↔ ∃ packets, Aligned Represents files packets ∧
      GeneralSourceRoleScopedShell292.run env fallback packets = some out := by
  constructor
  · intro pass
    obtain ⟨packets,staged,result⟩ := bind_success pass
    exact ⟨packets,(collect_exact _ _ make_exact _ _).mp staged,result⟩
  · rintro ⟨packets,related,result⟩
    unfold run
    rw [(collect_exact _ _ make_exact _ _).mpr related]
    exact result

def Origin {Scope : Type} (env : Scope → Environment) (files : List (Source Scope))
    (rid name : Nat) (term : Option Roles.Term) : Prop :=
  ∃ s ∈ files, ∃ roleName params,
    HeadShape s.head roleName params ∧ (env s.scope).role roleName = some rid ∧
      ∃ child, Child.typeDecl child ∈ s.body ∧ ∃ member : Output,
        Admitted .roleBodyDirect child member ∧
        (env s.scope).output rid member.spelling = some name ∧
        ResolvedBody (env s.scope) params member.body term

theorem assoc_exact {Scope : Type} (env : Scope → Environment) (fallback : Nat)
    (files : List (Source Scope)) (out : RoleSource) (h : run env fallback files = some out)
    (rid name : Nat) (term : Option Roles.Term) :
    (roleTable out rid).assoc name = some term ↔ Origin env files rid name term := by
  obtain ⟨packets,related,source⟩ := (run_exact ..).mp h
  rw [GeneralSourceRoleScopedShell292.source_scope_exact source]
  constructor
  · rintro ⟨p,inPackets,roleID,c,inList,o,syntaxOK,naming,bodyOK⟩
    obtain ⟨s,inFiles,scope,body,headShape⟩ := aligned_right related inPackets
    exact ⟨s,inFiles,p.source.name,p.source.parameters,headShape,
      scope ▸ roleID,c,body ▸ inList,o,syntaxOK,scope ▸ naming,scope ▸ bodyOK⟩
  · rintro ⟨s,inFiles,r,params,headOK,roleID,c,inList,o,syntaxOK,naming,bodyOK⟩
    obtain ⟨p,inPackets,scope,body,headShape⟩ := aligned_left related inFiles
    have e := Option.some.inj (((GeneralSourceRoleHeadShape292.head_exact ..).mpr headShape).symm.trans
      ((GeneralSourceRoleHeadShape292.head_exact ..).mpr headOK))
    have same := Prod.mk.inj e
    rw [← scope,← same.1] at roleID
    rw [← scope,← same.2] at bodyOK
    exact ⟨p,inPackets,roleID,c,body.symm ▸ inList,o,syntaxOK,scope.symm ▸ naming,bodyOK⟩

end Yulang.GeneralSourceRoleHeadPacketRun292
