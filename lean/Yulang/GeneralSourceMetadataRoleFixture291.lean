import Yulang.GeneralSourceMetadataRoleManifest291

/-! Attaching a finite role exporter to the original source recovers its
exact role map. An unused default is an independent closed control. -/
namespace Yulang.GeneralSourceMetadataRoleFixture291
open GeneralSourceMetadataRoles291
open GeneralSourceMetadataRoleManifest291 (manifestRows exact_manifest attached_manifest)
open GeneralSourceMetadataDefaults291 (Manifest coverageCheck coverage_exact)
open GeneralSourceMetadataFiniteLookup291 (get)
open GeneralRebaseRowChildSource287 (roles registry interp)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarations (Registry)

abbrev required : RoleRow := ⟨0,1,[(0,none)],by
  intro name rhs h; have e := List.mem_singleton.mp h; cases e⟩
abbrev fixture : RoleSource := ⟨1,[required]⟩

theorem actual_role_table : roleTable fixture = roles := by
  funext role
  by_cases zero : role = 0
  · subst role
    apply role_ext _ _ rfl
    funext name
    rfl
  · simp [roleTable,index,GeneralSourceMetadataFiniteLookup291.get,zero,roles,fallback,GeneralDeclarationExamples.bareRole]

theorem actual_roles_valid : check fixture = true := by decide +kernel

theorem source_emits_no_defaults : manifestRows fixture = [] := rfl

theorem actual_role_manifest : Manifest roles (manifestRows fixture) :=
  attached_manifest fixture ((check_exact fixture).mp actual_roles_valid) roles actual_role_table

def extra (key : Nat) : RoleRow := ⟨17,1,[(0,some (.app key [.var 0]))],by
  intro n rhs h
  have bound := congrArg Prod.snd (List.mem_singleton.mp h)
  cases Option.some.inj bound
  exact Nat.le_refl 1⟩

def withDefault (key : Nat) : RoleSource := ⟨1,[required,extra key]⟩

def registryWithDefault (key : Nat) : Registry :=
  { registry true with roles := roleTable (withDefault key) }

theorem role_source_valid (key : Nat) : Valid (withDefault key) := by
  constructor
  · change ([0,17] : List Nat).Nodup
    decide +kernel
  · intro row member
    simp only [withDefault,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> change ([0] : List Nat).Nodup <;> decide +kernel

theorem emitted_unused_default (key : Nat) :
    manifestRows (withDefault key) = [⟨17,0,.app key [.var 0]⟩] := rfl

theorem default_controls :
    coverageCheck (registryWithDefault 0) interp (manifestRows (withDefault 0)) = true ∧
    coverageCheck (registryWithDefault 6) interp (manifestRows (withDefault 6)) = false ∧
    coverageCheck (registryWithDefault 6) interp [] = true := by decide +kernel

theorem omission_not_sound :
    Coverage (registryWithDefault 0) interp ∧
    ¬ Coverage (registryWithDefault 6) interp := by
  refine ⟨(coverage_exact _ _ _ (exact_manifest _ (role_source_valid 0))).mp default_controls.1,?_⟩
  intro bad
  have falsePositive := (coverage_exact _ _ _ (exact_manifest _ (role_source_valid 6))).mpr bad
  rw [default_controls.2.1] at falsePositive
  cases falsePositive

end Yulang.GeneralSourceMetadataRoleFixture291
