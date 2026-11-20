import Yulang.GeneralSourceMetadataDefaults291

/-! Same actual metadata in both original registries. Only the opaque
child branch belongs to this existing materialization coverage fragment. -/
namespace Yulang.GeneralSourceMetadataCoverageFixture291
open GeneralRebaseRowChildSource287
open GeneralSourceMetadataFixture291 (source source_interpretation)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataDefaults291 (Manifest coverageCheck coverage_exact)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralSourceMetadataDeclarations291 (explicitUses)

theorem no_role_defaults : Manifest roles [] := by
  intro role name rhs
  simp only [List.not_mem_nil,false_iff]
  unfold roles
  split
  · change ¬ (if name = 0 then some none else none) = some (some rhs)
    split <;> simp
  · intro impossible; cases impossible

theorem full_source_check (choice : Bool) :
    coverageCheck (registry choice) (interpretation source) [] = choice := by
  cases choice <;> decide +kernel

theorem source_coverage_exact (choice : Bool) :
    Coverage (registry choice) interp ↔ choice = true := by
  rw [← source_interpretation,← coverage_exact _ _ _ no_role_defaults,full_source_check]

theorem explicit_use_lists :
    explicitUses (registry true).declarations = [(0,1),(0,1),(0,1)] ∧
    explicitUses (registry false).declarations = [(0,1),(0,1),(0,1),(6,1)] := by decide +kernel

theorem same_metadata_different_coverage :
    GeneralNominalCandidates.Metadata (registry true) ctx ∧
    GeneralNominalCandidates.Metadata (registry false) ctx ∧
    Coverage (registry true) interp ∧ ¬ Coverage (registry false) interp := by
  exact ⟨GeneralSourceMetadataFixture291.actual_metadata true,
    GeneralSourceMetadataFixture291.actual_metadata false,
    (source_coverage_exact true).mpr rfl,
    (fun bad => by cases (source_coverage_exact false).mp bad)⟩

end Yulang.GeneralSourceMetadataCoverageFixture291
