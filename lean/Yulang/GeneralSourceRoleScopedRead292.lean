import Yulang.GeneralSourceRoleScopedExport292

/-! Readback under externally supplied scopes. The witness retains the scope
from the input, rather than recovering it from a numeric ID or short name. -/
namespace Yulang.GeneralSourceRoleScopedRead292
open GeneralSourceRoleSpelling292 (Environment ResolvedBody body_exact)
open GeneralSourceRoleScopedExport292 (ScopedRole lower lower_exact Witness)
open GeneralSourceRoleManifest292 (aligned_left aligned_right)
open GeneralSourceMetadataRoles291 (RoleSource roleTable index)
open GeneralSourceMetadataFiniteLookup291 (get some_sound some_complete)

def SourceAssoc {Scope : Type} (env : Scope → Environment) (inputs : List (ScopedRole Scope))
    (r n : Nat) (term : Option Roles.Term) : Prop :=
  ∃ entry ∈ inputs, (env entry.scope).role entry.role.spelling = some r ∧
    ∃ o ∈ entry.role.outputs, (env entry.scope).output r o.spelling = some n ∧
      ResolvedBody (env entry.scope) entry.role.binders o.body term

theorem site_exact {Scope : Type} {env : Scope → Environment} {fallback : Nat}
    {inputs : List (ScopedRole Scope)} {out : RoleSource}
    (success : lower env fallback inputs = some out) (r n : Nat) (term : Option Roles.Term) :
    (roleTable out r).assoc n = some term ↔ SourceAssoc env inputs r n term := by
  have facts := (lower_exact ..).mp success
  constructor
  · intro found
    unfold roleTable at found
    cases hit : get r (index out) with
    | none => rw [hit] at found; cases found
    | some row =>
      rw [hit] at found
      obtain ⟨member,same⟩ := GeneralSourceMetadataRoles291.indexed hit
      obtain ⟨entry,inSources,linked⟩ := aligned_right facts.2.1
        (List.mem_map.mpr ⟨row,member,rfl⟩)
      have pair : (n,term) ∈ row.outputs := some_sound found
      have w := linked.2.2.2
      obtain ⟨o,within,proof⟩ := aligned_right w pair
      exact ⟨entry,inSources,same ▸ linked.2.1,o,within,same ▸ proof.1,proof.2⟩
  · rintro ⟨entry,mem,correct,o,within,outputID,bodyOK⟩
    obtain ⟨raw,inRows,w⟩ := aligned_left facts.2.1 mem
    obtain ⟨row,inTable,rfl⟩ := List.mem_map.mp inRows
    have same : r = row.role := Option.some.inj (correct.symm.trans w.2.1)
    obtain ⟨pair,inRow,ow⟩ := aligned_left w.2.2.2 within
    have outName : n = pair.1 := Option.some.inj ((same ▸ outputID).symm.trans ow.1)
    have value : pair.2 = term := Option.some.inj
      (((body_exact ..).mpr ow.2).symm.trans ((body_exact ..).mpr bodyOK))
    have p : pair = (n,term) := Prod.ext outName.symm value
    have found := some_complete (facts.2.2.2 row inTable) (p ▸ inRow)
    unfold roleTable
    rw [same, GeneralSourceMetadataRoles291.lookup_row facts.2.2 inTable]
    exact found

end Yulang.GeneralSourceRoleScopedRead292
