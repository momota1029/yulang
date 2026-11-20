import Yulang.GeneralSourceRoleUniqueSource292

/-! Separate an absent role from the existing total role function's fallback.
A fallback arity is not evidence of a source declaration. -/
namespace Yulang.GeneralSourceRoleArityRead292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleScopedExport292 (ScopedRole lower lower_exact Witness)
open GeneralSourceRoleManifest292 (aligned_left aligned_right)
open GeneralSourceMetadataRoles291 (RoleSource RoleRow roleTable index)
open GeneralSourceMetadataBareRole291 (forgetRow)
open GeneralSourceMetadataFiniteLookup291 (get)

def Declares {Scope : Type} (env : Scope → Environment) (input : List (ScopedRole Scope))
    (key : Nat) (sourceArity : Nat) : Prop :=
  ∃ declared ∈ input, (env declared.scope).role declared.role.spelling = some key ∧
    declared.role.binders.length = sourceArity

theorem present_exact {Scope : Type} {env : Scope → Environment} {input : List (ScopedRole Scope)}
    {fallback : Nat} {out : RoleSource} (assembled : lower env fallback input = some out)
    (key : Nat) (arity : Nat) :
    (∃ row, get key (index out) = some row ∧ row.arity = arity) ↔ Declares env input key arity := by
  have facts := (lower_exact ..).mp assembled
  constructor
  · rintro ⟨row,lookup,thatArity⟩
    have ⟨member,keyEq⟩ := GeneralSourceMetadataRoles291.indexed lookup
    obtain ⟨entry,inSource,witness⟩ :=
      aligned_right facts.2.1 (List.mem_map.mpr ⟨row,member,rfl⟩)
    have a : entry.role.binders.length = row.arity := witness.2.2.1
    exact ⟨entry,inSource,keyEq ▸ witness.2.1,a.trans thatArity⟩
  · rintro ⟨entry,fromInput,roleID,declaredArity⟩
    obtain ⟨raw,member,witness⟩ := aligned_left facts.2.1 fromInput
    obtain ⟨row,inTable,rfl⟩ := List.mem_map.mp member
    have same : key = row.role := Option.some.inj (roleID.symm.trans witness.2.1)
    have len : entry.role.binders.length = row.arity := witness.2.2.1
    exact ⟨row,same.symm ▸ GeneralSourceMetadataRoles291.lookup_row facts.2.2 inTable,
      len.symm.trans declaredArity⟩

theorem absent_exact {Scope : Type} {env : Scope → Environment} {input : List (ScopedRole Scope)}
    {fallback : Nat} {out : RoleSource} (assembled : lower env fallback input = some out)
    (key : Nat) : get key (index out) = none ↔ ∀ arity, ¬ Declares env input key arity := by
  constructor
  · intro no arity decl
    obtain ⟨row,yes,_⟩ := (present_exact assembled key arity).mpr decl
    rw [no] at yes; cases yes
  · intro no
    cases found : get key (index out) with
    | none => rfl
    | some row => exact False.elim (no row.arity
        ((present_exact assembled key row.arity).mp ⟨row,found,rfl⟩))

theorem declared_readback {Scope : Type} {env : Scope → Environment} {input : List (ScopedRole Scope)}
    {fallback : Nat} {out : RoleSource} (assembled : lower env fallback input = some out)
    (key arity : Nat) (known : Declares env input key arity) : (roleTable out key).arity = arity := by
  obtain ⟨row,read,rfl⟩ := (present_exact assembled key arity).mpr known
  simp [roleTable,read,RoleRow.interpret]

theorem fallback_readback {Scope : Type} {env : Scope → Environment} {input : List (ScopedRole Scope)}
    {fallback : Nat} {out : RoleSource} (assembled : lower env fallback input = some out)
    (key : Nat) (unknown : ∀ arity, ¬ Declares env input key arity) :
    (roleTable out key).arity = fallback ∧ ∀ name, (roleTable out key).assoc name = none := by
  have gone := (absent_exact assembled key).mpr unknown
  have stored := ((lower_exact ..).mp assembled).1
  simp [roleTable,gone,GeneralSourceMetadataRoles291.fallback,stored]

end Yulang.GeneralSourceRoleArityRead292
