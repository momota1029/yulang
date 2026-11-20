import Yulang.GeneralSourceMetadataBareRole291

/-! The executable role-table constructor validates positional scope and
duplicate names. The accepted table erases to exactly the original data. -/
namespace Yulang.GeneralSourceMetadataBuildRoles291
open GeneralSourceMetadataBareRole291
open GeneralSourceMetadataRoles291 (RoleSource Valid check check_exact)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure Input where
  fallbackArity : Nat
  rows : List BareRow

def forget (src : RoleSource) : Input := ⟨src.fallbackArity,src.rows.map forgetRow⟩

def build (raw : Input) : Option RoleSource :=
  (buildRows raw.rows).bind fun recovered =>
    let out : RoleSource := ⟨raw.fallbackArity,recovered⟩
    if check out then some out else none

theorem build_exact (raw : Input) (out : RoleSource) :
    build raw = some out ↔ forget out = raw ∧ Valid out := by
  constructor
  · intro accepted
    obtain ⟨rows,returned,dec⟩ := bind_success accepted
    let pick : RoleSource := ⟨raw.fallbackArity,rows⟩
    change (if check pick = true then some pick else none) = some out at dec
    have data := (list_exact raw.rows rows).mp returned
    by_cases valid : check pick = true
    · rw [ite_eq_left valid] at dec
      have same : pick = out := Option.some.inj dec
      subst out
      refine ⟨?_,(check_exact ..).mp valid⟩
      cases raw
      exact congrArg (Input.mk _) data
    · rw [ite_eq_right valid] at dec
      cases dec
  · rintro ⟨rfl,correct⟩
    have success := (list_exact ((forget out).rows) out.rows).mpr rfl
    unfold build
    rw [success]
    change (if check out = true then some out else none) = some out
    rw [ite_eq_left ((check_exact ..).mpr correct)]

theorem compiled_manifest (raw : Input) (out : RoleSource) (accepted : build raw = some out) :
    GeneralSourceMetadataDefaults291.Manifest (GeneralSourceMetadataRoles291.roleTable out)
      (GeneralSourceMetadataRoleManifest291.manifestRows out) :=
  GeneralSourceMetadataRoleManifest291.exact_manifest out ((build_exact raw out).mp accepted).2

end Yulang.GeneralSourceMetadataBuildRoles291
