import Yulang.GeneralSourceRoleExport292

/-! Exact origins of default manifest entries in accepted symbolic inputs.
An independent CST projection is still required to call them source sites. -/
namespace Yulang.GeneralSourceRoleManifest292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceMetadataDefaults291 (Default)
open GeneralSourceMetadataRoleManifest291 (manifestRows rowDefaults)

theorem aligned_left {A B : Type} {p : A → B → Prop} {xs : List A} {ys : List B}
    (h : Aligned p xs ys) {x : A} (m : x ∈ xs) :
    ∃ y ∈ ys, p x y := by
  induction h with
  | nil => cases m
  | cons head _ ih =>
    rcases List.mem_cons.mp m with same | rest
    · cases same
      exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨y,mem,related⟩ := ih rest
      exact ⟨y,List.mem_cons_of_mem _ mem,related⟩

theorem aligned_right {A B : Type} {p : A → B → Prop} {xs : List A} {ys : List B}
    (h : Aligned p xs ys) {y : B} (m : y ∈ ys) :
    ∃ x ∈ xs, p x y := by
  induction h with
  | nil => cases m
  | cons head _ ih =>
    rcases List.mem_cons.mp m with same | rest
    · cases same
      exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨x,mem,related⟩ := ih rest
      exact ⟨x,List.mem_cons_of_mem _ mem,related⟩

def Origin (env : Environment) (inputs : List Role) (d : Default) : Prop :=
  ∃ r ∈ inputs, env.role r.spelling = some d.role ∧
    ∃ o ∈ r.outputs, env.output d.role o.spelling = some d.name ∧
      ResolvedBody env r.binders o.body (some d.body)

theorem manifest_exact {env : Environment} {fallback : Nat} {inputs : List Role}
    {out : RoleSource} (accepted : lower env fallback inputs = some out) (d : Default) :
    d ∈ manifestRows out ↔ Origin env inputs d := by
  have facts := (lower_exact env fallback inputs out).mp accepted
  constructor
  · intro member
    obtain ⟨row,inTable,inRow⟩ := List.mem_flatMap.mp member
    obtain ⟨same,pair⟩ := (GeneralSourceMetadataRoleManifest291.row_exact row d).mp inRow
    obtain ⟨r,inInputs,w⟩ := aligned_right facts.2.1
      (List.mem_map.mpr ⟨row,inTable,rfl⟩)
    obtain ⟨o,inRole,sem⟩ := aligned_right w.2.2.2 pair
    exact ⟨r,inInputs,same.symm ▸ w.2.1,o,inRole,same.symm ▸ sem.1,sem.2⟩
  · rintro ⟨r,inInputs,roleID,o,inRole,nameID,resolved⟩
    obtain ⟨rowRaw,member,related⟩ := aligned_left facts.2.1 inInputs
    obtain ⟨row,inTable,rfl⟩ := List.mem_map.mp member
    have eq := Option.some.inj (roleID.symm.trans related.2.1)
    obtain ⟨pair,inRow,how⟩ := aligned_left related.2.2.2 inRole
    have nameEq : d.name = pair.1 := Option.some.inj ((eq ▸ nameID).symm.trans how.1)
    have valueEq : pair.2 = some d.body := Option.some.inj
      (((body_exact ..).mpr how.2).symm.trans ((body_exact ..).mpr resolved))
    have pairEq : pair = (d.name,some d.body) := Prod.ext nameEq.symm valueEq
    exact List.mem_flatMap.mpr ⟨row,inTable,
      (GeneralSourceMetadataRoleManifest291.row_exact row d).mpr ⟨eq,pairEq ▸ inRow⟩⟩

theorem runtime_default_exact {env : Environment} {fallback : Nat} {inputs : List Role}
    {out : RoleSource} (accepted : lower env fallback inputs = some out)
    (role name : Nat) (rhs : Roles.Term) :
    (roleTable out role).assoc name = some (some rhs) ↔ Origin env inputs ⟨role,name,rhs⟩ := by
  have facts := (lower_exact env fallback inputs out).mp accepted
  exact ((GeneralSourceMetadataRoleManifest291.exact_manifest out facts.2.2) role name rhs).symm.trans
    (manifest_exact accepted ⟨role,name,rhs⟩)

end Yulang.GeneralSourceRoleManifest292
