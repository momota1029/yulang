import Yulang.GeneralSourceMetadataBareBundle291

/-! Two independent data-only controls: invalid lexical scope and valid
scope but unsupported materialization must not be conflated. -/
namespace Yulang.GeneralSourceMetadataBareFixture291
open GeneralSourceMetadataBuildRoles291 (Input build)
open GeneralSourceMetadataBareBundle291 (InputBundle run forget reassemble)
open GeneralSourceMetadataBundle291 (Certificate)
open GeneralSourceMetadataBundleFixture291 (actual executable_both)
open GeneralSourceMetadataRoleFixture291 (fixture actual_roles_valid withDefault role_source_valid)

abbrev outOfScope : Input := ⟨1,[⟨17,1,[(0,some (.var 1))]⟩]⟩
abbrev duplicateRole : Input := ⟨1,[⟨17,1,[]⟩,⟨17,1,[]⟩]⟩
abbrev duplicateOutput : Input := ⟨1,[⟨17,1,[(0,none),(0,none)]⟩]⟩

theorem raw_role_controls :
    (build outOfScope).isSome = false ∧ (build duplicateRole).isSome = false ∧
    (build duplicateOutput).isSome = false := by decide +kernel

theorem well_scoped_not_coverage :
    (build (GeneralSourceMetadataBuildRoles291.forget (withDefault 6))).isSome = true ∧
    ¬ GeneralNominalCenteredHeadWFSource.Coverage
      (GeneralSourceMetadataRoleFixture291.registryWithDefault 6) GeneralRebaseRowChildSource287.interp := by
  have compiled := (GeneralSourceMetadataBuildRoles291.build_exact _ _).mpr ⟨rfl,role_source_valid 6⟩
  rw [compiled]
  exact ⟨rfl,GeneralSourceMetadataRoleFixture291.omission_not_sound.2⟩

theorem actual_exec (choice : Bool) :
    (run (forget (actual choice))).map Certificate.ready = some choice := by
  unfold run
  rw [reassemble (actual choice) ((GeneralSourceMetadataRoles291.check_exact fixture).mp actual_roles_valid)]
  exact congrArg some (executable_both choice)

end Yulang.GeneralSourceMetadataBareFixture291
