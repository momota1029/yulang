import Yulang.GeneralStoppedLiteralCompiler335
import Yulang.GeneralCanonicalChildOrder

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedCanonical335
open GeneralDeclarations (Registry Declaration DeclarationChecked Checked)
open GeneralRegistryReordering (Reorders DeclarationReorders)
open GeneralCanonicalChildOrder (canonicalDeclaration canonicalRequirements_perm canonical_declaration_eq)
open GeneralNominalCenteredHeadWFSource (Coverage coverage_reorders)
open CommonRoleOutermostResolver (All₂)

def sourceCanonical (r : Registry) : Registry :=
  { r with declarations := r.declarations.map canonicalDeclaration }

theorem declaration_reorders (d : Declaration) : DeclarationReorders d (canonicalDeclaration d) :=
  ⟨rfl,rfl,rfl,canonicalRequirements_perm _,rfl,rfl⟩

theorem source_reorders (r : Registry) : Reorders r (sourceCanonical r) := by
  refine ⟨rfl,rfl,r.declarations,List.Perm.refl _,?_⟩
  have all (ds : List Declaration) : All₂ DeclarationReorders ds (ds.map canonicalDeclaration) := by
    induction ds with
    | nil => exact .nil
    | cons d rest ih => exact .cons (declaration_reorders d) ih
  exact all _

theorem source_checked (c : Checked r) : Checked (sourceCanonical r) := by
  constructor
  · change ((r.declarations.map canonicalDeclaration).map Declaration.id).Nodup
    rw [List.map_map]
    exact c.1
  · intro declaration visible
    obtain ⟨original,old,rfl⟩ := List.mem_map.mp visible
    exact GeneralCanonicalChildOrder.canonical_checked original (c.2 _ old)

theorem source_coverage (c : Coverage r i) : Coverage (sourceCanonical r) i :=
  coverage_reorders (source_reorders _) c

/-- Canonical replay is an opt-in projection, not a change to the
current declaration order. Compared versions use the same exact
ordinary slice/capture/target table, and only source order differs. -/
theorem ordinary_canonical_eq (first last : Declaration) (order : DeclarationReorders first last)
    (checked : DeclarationChecked r.constructors r.roles first) :
    GeneralDeclarativeNestedBody332.compileBody r i d (canonicalDeclaration first) s spans keep fallback targets =
      GeneralDeclarativeNestedBody332.compileBody r i d (canonicalDeclaration last) s spans keep fallback targets := by
  rw [canonical_declaration_eq order checked.identified.1]

theorem literal_canonical_eq (first last : Declaration) (order : DeclarationReorders first last)
    (checked : DeclarationChecked r.constructors r.roles first) :
    GeneralStoppedLiteralCompiler335.compile r i d (canonicalDeclaration first) s spans keep fallback targets =
      GeneralStoppedLiteralCompiler335.compile r i d (canonicalDeclaration last) s spans keep fallback targets := by
  rw [canonical_declaration_eq order checked.identified.1]

end Yulang.GeneralStoppedCanonical335
