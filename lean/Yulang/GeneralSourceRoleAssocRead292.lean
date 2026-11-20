import Yulang.GeneralSourceRoleManifest292

/-! Exact readback for all three states of a resolved association after a
successful symbolic lowering: undeclared, required, or defaulted. -/
namespace Yulang.GeneralSourceRoleAssocRead292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292
open GeneralSourceRoleManifest292 (aligned_left aligned_right)
open GeneralSourceMetadataRoles291 (RoleSource roleTable index Valid)
open GeneralSourceMetadataFiniteLookup291 (get some_sound some_complete)

def DeclaredAt (env : Environment) (input : List Role) (role name : Nat)
    (term : Option Roles.Term) : Prop :=
  ∃ r ∈ input, env.role r.spelling = some role ∧
    ∃ o ∈ r.outputs, env.output role o.spelling = some name ∧
      ResolvedBody env r.binders o.body term

theorem assoc_exact {env : Environment} {fallback : Nat} {input : List Role}
    {out : RoleSource} (h : lower env fallback input = some out)
    (r n : Nat) (value : Option Roles.Term) :
    (roleTable out r).assoc n = some value ↔ DeclaredAt env input r n value := by
  have facts := (lower_exact ..).mp h
  constructor
  · intro found
    unfold roleTable at found
    cases hit : get r (index out) with
    | none => rw [hit] at found; cases found
    | some row =>
      rw [hit] at found
      obtain ⟨member,same⟩ := GeneralSourceMetadataRoles291.indexed hit
      obtain ⟨source,inInput,w⟩ := aligned_right facts.2.1
        (List.mem_map.mpr ⟨row,member,rfl⟩)
      have pair : (n,value) ∈ row.outputs := some_sound found
      obtain ⟨o,inRole,ow⟩ := aligned_right w.2.2.2 pair
      exact ⟨source,inInput,same ▸ w.2.1,o,inRole,same ▸ ow.1,ow.2⟩
  · rintro ⟨source,mem,correct,o,inRole,outputID,bodyOK⟩
    obtain ⟨raw,inRows,w⟩ := aligned_left facts.2.1 mem
    obtain ⟨row,inTable,rfl⟩ := List.mem_map.mp inRows
    have same : r = row.role := Option.some.inj (correct.symm.trans w.2.1)
    obtain ⟨pair,inRow,ow⟩ := aligned_left w.2.2.2 inRole
    have nameID : n = pair.1 := Option.some.inj ((same ▸ outputID).symm.trans ow.1)
    have sameValue : pair.2 = value := Option.some.inj
      (((body_exact ..).mpr ow.2).symm.trans ((body_exact ..).mpr bodyOK))
    have samePair : pair = (n,value) := Prod.ext nameID.symm sameValue
    have found := some_complete (facts.2.2.2 row inTable) (samePair ▸ inRow)
    unfold roleTable
    rw [same, GeneralSourceMetadataRoles291.lookup_row facts.2.2 inTable]
    exact found

theorem undeclared_exact {env : Environment} {fallback : Nat} {input : List Role}
    {out : RoleSource} (h : lower env fallback input = some out) (r n : Nat) :
    (roleTable out r).assoc n = none ↔ ∀ value, ¬ DeclaredAt env input r n value := by
  constructor
  · intro absent value w
    have read := (assoc_exact h r n value).mpr w
    rw [absent] at read
    cases read
  · intro notThere
    cases read : (roleTable out r).assoc n with
    | none => rfl
    | some value => exact False.elim (notThere value ((assoc_exact h ..).mp read))

theorem required_exact {env : Environment} {fallback : Nat} {input : List Role}
    {out : RoleSource} (h : lower env fallback input = some out) (r n : Nat) :
    (roleTable out r).assoc n = some none ↔
      ∃ source ∈ input, env.role source.spelling = some r ∧
        ∃ o ∈ source.outputs, env.output r o.spelling = some n ∧ o.body = .required := by
  rw [assoc_exact h]
  constructor
  · rintro ⟨source,member,hit,o,inRole,outputID,bodyOK⟩
    rcases o with ⟨spelling, form⟩
    change ResolvedBody env source.binders form none at bodyOK
    cases bodyOK
    exact ⟨source,member,hit,⟨spelling,.required⟩,inRole,outputID,rfl⟩
  · rintro ⟨source,member,hit,o,inRole,outputID,form⟩
    refine ⟨source,member,hit,o,inRole,outputID,?_⟩
    rw [form]
    exact .required

end Yulang.GeneralSourceRoleAssocRead292
