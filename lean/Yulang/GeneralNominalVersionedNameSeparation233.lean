import Yulang.GeneralNominalAggregateVersion231
set_option backward.isDefEq.respectTransparency false
/-! Full ownership/version separation needed by a future general witness
extension: collisions identify root, declaration, purpose, variable and the
ordered endpoint list. This does not assert finite reachable version bounds. -/
namespace Yulang.GeneralNominalVersionedNameSeparation233
open GeneralNominalAggregateVersion231
open GeneralNominalIdentities
open GeneralNominalAllocation (Bindings occurrences)

theorem key_identity : key root declaration purpose name first = key other otherDeclaration otherPurpose otherName last ↔
    root = other ∧ declaration = otherDeclaration ∧ purpose = otherPurpose ∧ name = otherName ∧
    occurrences first name = occurrences last otherName := by
  constructor
  · intro equal
    have roots := congrArg (fun k : Origin => k.1) equal
    have declarations := congrArg (fun k : Origin => k.2.1) equal
    have purposes := congrArg (fun k : Origin => k.2.2.1) equal
    have names := congrArg (fun k : Origin => k.2.2.2.1) equal
    change root = other at roots
    change declaration = otherDeclaration at declarations
    change purpose = otherPurpose at purposes
    change name = otherName at names
    refine ⟨roots,declarations,purposes,names,?_⟩
    subst other
    subst otherDeclaration
    subst otherPurpose
    subst otherName
    exact (key_eq_iff root declaration purpose name).mp equal
  · rintro ⟨rfl,rfl,rfl,rfl,same⟩
    exact (key_eq_iff ..).mpr same

theorem slot_identity : slot seed root declaration purpose name first =
    slot seed other otherDeclaration otherPurpose otherName last ↔
    root = other ∧ declaration = otherDeclaration ∧ purpose = otherPurpose ∧ name = otherName ∧
    occurrences first name = occurrences last otherName :=
  (source_identity seed _ _).trans key_identity

theorem other_root (different : root ≠ other) : slot seed root declaration purpose name first ≠
    slot seed other otherDeclaration otherPurpose otherName last := fun same => different (slot_identity.mp same).1

theorem other_declaration (different : declaration ≠ otherDeclaration) : slot seed root declaration purpose name first ≠
    slot seed other otherDeclaration otherPurpose otherName last := fun same => different (slot_identity.mp same).2.1

theorem other_name (different : name ≠ otherName) : slot seed root declaration purpose name first ≠
    slot seed other otherDeclaration otherPurpose otherName last := fun same => different (slot_identity.mp same).2.2.2.1

theorem other_endpoints (different : occurrences first name ≠ occurrences last otherName) :
    slot seed root declaration purpose name first ≠ slot seed other otherDeclaration otherPurpose otherName last :=
  fun same => different (slot_identity.mp same).2.2.2.2

/-- No ownership key or version in the stated finite history is overwritten.
The hypothesis names the independently checkable ownership/endpoints mismatch;
it does not assume the required model extension or dictionary conclusion. -/
theorem outside_history
    (history : List (Nat × Nat × Nat × Nat × Bindings))
    (separate : ∀ prior ∈ history, root ≠ prior.1 ∨ declaration ≠ prior.2.1 ∨
      purpose ≠ prior.2.2.1 ∨ name ≠ prior.2.2.2.1 ∨
      occurrences first name ≠ occurrences prior.2.2.2.2 prior.2.2.2.1) :
    slot seed root declaration purpose name first ∉
      history.map (fun prior => slot seed prior.1 prior.2.1 prior.2.2.1 prior.2.2.2.1 prior.2.2.2.2) := by
  intro member
  obtain ⟨prior,present,equal⟩ := List.mem_map.mp member
  have same := slot_identity.mp equal.symm
  rcases separate prior present with bad | bad | bad | bad | bad
  · exact bad same.1
  · exact bad same.2.1
  · exact bad same.2.2.1
  · exact bad same.2.2.2.1
  · exact bad same.2.2.2.2

end Yulang.GeneralNominalVersionedNameSeparation233
