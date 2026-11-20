import Yulang.GeneralSourceRoleAttach292
import Yulang.GeneralSourceMetadataDiagnosticProvenance291

/-! Reconstruct symbolic ownership of the existing role-default diagnostics,
without mapping them to fabricated source spans or changing their meaning. -/
namespace Yulang.GeneralSourceRoleDiagnosticLink292
open GeneralSourceRoleSpelling292 (Environment Output ResolvedBody)
open GeneralSourceRoleSyntaxBoundary292 (Shell Admitted Owner)
open GeneralSourceRoleSyntaxPipeline292 (default_from_shells)
open GeneralSourceRoleAttach292 (Input compose)
open GeneralSourceMetadataBundle291 (SourceBundle registry inspect)
open GeneralSourceMetadataDiagnostics291 (Failure diagnostics)
open GeneralSourceMetadataSites291 (Entry sourceSites tag)
open GeneralSourceMetadataUse291 (Use)
open GeneralSourceMetadataProblem291 (Problem problem)
open GeneralSourceMetadataSyntax291 (terms)
open GeneralSourceMetadataRoleManifest291 (manifestRows)

theorem role_use_exact (ds : List GeneralDeclarations.Declaration)
    (defaults : List GeneralSourceMetadataDefaults291.Default) (r n : Nat) (q : Use) :
    (⟨.roleDefault r n,q⟩ : Entry) ∈ sourceSites ds defaults ↔
      ∃ rhs, ⟨r,n,rhs⟩ ∈ defaults ∧ q ∈ terms rhs := by
  have noHead : ∀ d : GeneralDeclarations.Declaration, ∀ e,
      e ∈ GeneralSourceMetadataSites291.declarationSites d → e.site ≠ .roleDefault r n := by
    intro d e h equal
    unfold GeneralSourceMetadataSites291.declarationSites at h
    rw [List.mem_append,List.mem_append] at h
    rcases h with (head | whereSite) | assoc
    · obtain ⟨_,_,a⟩ := List.mem_map.mp head
      rw [← a] at equal
      cases equal
    · obtain ⟨clause,_,inside⟩ := List.mem_flatMap.mp whereSite
      rw [GeneralSourceMetadataSites291.clauseSites,List.mem_append] at inside
      rcases inside with inputs | outs
      · obtain ⟨_,_,a⟩ := List.mem_map.mp inputs
        rw [← a] at equal
        cases equal
      · obtain ⟨_,_,item⟩ := List.mem_flatMap.mp outs
        obtain ⟨_,_,a⟩ := List.mem_map.mp item
        rw [← a] at equal
        cases equal
    · obtain ⟨_,_,inside⟩ := List.mem_flatMap.mp assoc
      obtain ⟨_,_,a⟩ := List.mem_map.mp inside
      rw [← a] at equal
      cases equal
  unfold sourceSites
  constructor
  · intro found
    rcases List.mem_append.mp found with explicit | default
    · obtain ⟨d,_,item⟩ := List.mem_flatMap.mp explicit
      exact False.elim (noHead d _ item rfl)
    · obtain ⟨d,inManifest,site⟩ := List.mem_flatMap.mp default
      obtain ⟨value,inBody,exactSite⟩ := List.mem_map.mp site
      have ids : d.role = r ∧ d.name = n ∧ value = q := by
        simpa only [Entry.mk.injEq,GeneralSourceMetadataSites291.Site.roleDefault.injEq,and_assoc] using exactSite
      obtain ⟨role,name,body⟩ := d
      change role = r ∧ name = n ∧ value = q at ids
      rcases ids with ⟨rfl,rfl,rfl⟩
      exact ⟨body,inManifest,inBody⟩
  · rintro ⟨rhs,member,used⟩
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨⟨r,n,rhs⟩,member,List.mem_map.mpr ⟨q,used,rfl⟩⟩)

theorem default_issue_exact {env : Environment} {input : Input} {out : SourceBundle}
    (accepted : compose env input = some out) (rid name : Nat) (use : Use) (why : Problem) :
    (⟨⟨.roleDefault rid name,use⟩,why⟩ : Failure) ∈ (inspect out).unsupported ↔
       problem (registry out).constructors
          (GeneralSourceMetadataRows291.interpretation out.snapshot) use = some why ∧
       ∃ s ∈ input.shells, env.role s.name = some rid ∧
         ∃ el ∈ s.directTypeChildren, ∃ o : Output,
           Admitted .roleBodyDirect el o ∧ env.output rid o.spelling = some name ∧
           ∃ rhs, ResolvedBody env s.parameters o.body (some rhs) ∧ use ∈ terms rhs := by
  have built := ((GeneralSourceRoleAttach292.assemble_exact ..).mp accepted).2.2.2
  have valid := ((GeneralSourceRoleSyntaxPipeline292.pipeline_exact ..).mp built).choose_spec.2.2.2
  change (⟨⟨.roleDefault rid name,use⟩,why⟩ : Failure) ∈
    diagnostics (registry out) (GeneralSourceMetadataRows291.interpretation out.snapshot)
      (manifestRows out.roles) ↔ _
  rw [GeneralSourceMetadataDiagnosticProvenance291.exact_origin]
  simp only
  rw [role_use_exact]
  constructor
  · rintro ⟨⟨rhs,member,queried⟩,reason⟩
    have lookup := (GeneralSourceMetadataRoleManifest291.exact_manifest out.roles valid
      rid name rhs).mp member
    obtain ⟨shell,inInput,roleID,ele,inShell,o,admitted,nameID,bodyOK⟩ :=
      (default_from_shells env input.fallbackArity input.shells out.roles built rid name rhs).mp lookup
    exact ⟨reason,shell,inInput,roleID,ele,inShell,o,admitted,nameID,rhs,bodyOK,queried⟩
  · rintro ⟨reason,shell,inInput,roleID,ele,inShell,o,admitted,nameID,rhs,bodyOK,queried⟩
    have lookup := (default_from_shells env input.fallbackArity input.shells out.roles built rid name rhs).mpr
      ⟨shell,inInput,roleID,ele,inShell,o,admitted,nameID,bodyOK⟩
    exact ⟨⟨rhs,(GeneralSourceMetadataRoleManifest291.exact_manifest out.roles valid rid name rhs).mpr
      lookup,queried⟩,reason⟩

end Yulang.GeneralSourceRoleDiagnosticLink292
