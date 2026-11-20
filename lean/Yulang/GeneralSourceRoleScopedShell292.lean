import Yulang.GeneralSourceRoleScopedFixture292
import Yulang.GeneralSourceRoleCoveredShell292

/-! Scope plus checked direct member enumeration, before symbol resolution.
The assigned scope and full member list are independent caller evidence. -/
namespace Yulang.GeneralSourceRoleScopedShell292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (projectRole)
open GeneralSourceRoleCoveredShell292 (Inventory prepare Checked prepare_exact)
open GeneralSourceRoleScopedExport292 (ScopedRole lower)
open GeneralSourceRoleExport292 (Aligned collect collect_exact)
open GeneralSourceRoleSyntaxPipeline292 (ShellWitness)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure Packet (Scope : Type) where
  scope : Scope
  source : Inventory

def project {Scope : Type} (p : Packet Scope) : Option (ScopedRole Scope) :=
  (prepare p.source).bind fun shell => (projectRole shell).map fun role =>
    ⟨p.scope,role⟩

def Represents {Scope : Type} (p : Packet Scope) (out : ScopedRole Scope) : Prop :=
  p.scope = out.scope ∧
    ∃ shell, Checked p.source shell ∧ ShellWitness shell out.role

theorem project_exact {Scope : Type} (p : Packet Scope) (out : ScopedRole Scope) :
    project p = some out ↔ Represents p out := by
  constructor
  · intro eq
    obtain ⟨shell,supplied,mapping⟩ := bind_success eq
    rcases out with ⟨scope,role⟩
    change (projectRole shell).map (fun role => (⟨p.scope,role⟩ : ScopedRole Scope)) =
      some ⟨scope,role⟩ at mapping
    cases h : projectRole shell with
    | none => simp [h] at mapping
    | some r =>
      have same : p.scope = scope ∧ r = role := by simpa [h,ScopedRole.mk.injEq] using mapping
      exact ⟨same.1,shell,(prepare_exact ..).mp supplied,
        (GeneralSourceRoleSyntaxBoundary292.projectRole_exact ..).mp (same.2 ▸ h)⟩
  · rintro ⟨tag,shell,ok,shaped⟩
    have read := (GeneralSourceRoleSyntaxBoundary292.projectRole_exact ..).mpr shaped
    unfold project
    rw [(prepare_exact ..).mpr ok,Option.bind_some,read,Option.map_some]
    rcases out with ⟨scope,role⟩
    exact congrArg some (congrArg (fun s => ScopedRole.mk s role) tag)

def run {Scope : Type} (env : Scope → Environment) (fallback : Nat)
    (packets : List (Packet Scope)) : Option RoleSource :=
  (collect project packets).bind (lower env fallback)

theorem run_exact {Scope : Type} (env : Scope → Environment) (fallback : Nat)
    (packets : List (Packet Scope)) (out : RoleSource) :
    run env fallback packets = some out ↔ ∃ entries, Aligned Represents packets entries ∧
      lower env fallback entries = some out := by
  constructor
  · intro pass
    obtain ⟨entries,ready,result⟩ := bind_success pass
    exact ⟨entries,(collect_exact _ _ project_exact _ _).mp ready,result⟩
  · rintro ⟨entries,linked,result⟩
    unfold run
    rw [(collect_exact _ _ project_exact _ _).mpr linked]
    exact result

theorem source_scope_exact {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {packets : List (Packet Scope)} {out : RoleSource}
    (accepted : run env fallback packets = some out) (r n : Nat) (term : Option Roles.Term) :
    (GeneralSourceMetadataRoles291.roleTable out r).assoc n = some term ↔
      ∃ p ∈ packets, (env p.scope).role p.source.name = some r ∧
        ∃ el, GeneralSourceRoleChildCoverage292.Child.typeDecl el ∈ p.source.directChildren ∧
          ∃ o, GeneralSourceRoleSyntaxBoundary292.Admitted .roleBodyDirect el o ∧
            (env p.scope).output r o.spelling = some n ∧
            GeneralSourceRoleSpelling292.ResolvedBody (env p.scope) p.source.parameters o.body term := by
  have ⟨entries,transfer,recorded⟩ := (run_exact ..).mp accepted
  rw [GeneralSourceRoleScopedRead292.site_exact recorded]
  constructor
  · rintro ⟨input,inEntries,found,o,inRole,nameOK,bodyOK⟩
    obtain ⟨p,inPackets,same,shell,inventory,shapeOK⟩ :=
      GeneralSourceRoleManifest292.aligned_right transfer inEntries
    obtain ⟨el,inShell,adm⟩ := GeneralSourceRoleManifest292.aligned_right shapeOK.2.2 inRole
    have inPacket := (GeneralSourceRoleChildCoverage292.member_exact inventory.2.2 el).mp inShell
    rw [← same,← shapeOK.1,← inventory.1] at found
    rw [← same,← shapeOK.2.1,← inventory.2.1] at bodyOK
    exact ⟨p,inPackets,found,el,inPacket,o,adm,same.symm ▸ nameOK,bodyOK⟩
  · rintro ⟨p,inPackets,found,el,inPacket,o,adm,nameOK,bodyOK⟩
    obtain ⟨input,inEntries,same,shell,inventory,shapeOK⟩ :=
      GeneralSourceRoleManifest292.aligned_left transfer inPackets
    have inShell := (GeneralSourceRoleChildCoverage292.member_exact inventory.2.2 el).mpr inPacket
    obtain ⟨o',inRole,rel⟩ := GeneralSourceRoleManifest292.aligned_left shapeOK.2.2 inShell
    have identical : o = o' := Option.some.inj
      (((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr adm).symm.trans
        ((GeneralSourceRoleSyntaxBoundary292.projection_exact ..).mpr rel))
    subst o'
    rw [same,inventory.1,shapeOK.1] at found
    rw [same,inventory.2.1,shapeOK.2.1] at bodyOK
    exact ⟨input,inEntries,found,o,inRole,same ▸ nameOK,bodyOK⟩

end Yulang.GeneralSourceRoleScopedShell292
