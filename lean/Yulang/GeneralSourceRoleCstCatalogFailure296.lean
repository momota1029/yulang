import Yulang.GeneralSourceRoleCstRecoveredCatalog296

/-! A failure identifies the first unsupported demanded key, in the old
ordered query trace, not an arbitrary missing catalog entry. -/
namespace Yulang.GeneralSourceRoleCstCatalogFailure296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup fiber empty_exact ambiguous_exact)
open GeneralSourceRoleCstCatalogTrace296 (Issue requireAll Supported)
open GeneralSourceRoleCstNamingRequests295 (Query)

def Bad (c : Catalog) (q : Query) : Issue → Prop
  | .missing k => k = q ∧ fiber c q = []
  | .ambiguous k => k = q ∧ 2 ≤ (fiber c q).length

theorem fails_at_prefix (c : Catalog) (pre rest : List Query) (q : Query) (why : Issue)
    (earlier : Supported c pre) (bad : Bad c q why) :
    requireAll c (pre ++ q::rest) = .error why := by
  induction pre with
  | nil =>
    cases why with
    | missing k =>
      obtain ⟨rfl,empty⟩ := bad
      simp [requireAll,(empty_exact ..).mpr empty]
    | ambiguous k =>
      obtain ⟨rfl,n⟩ := bad
      simp [requireAll,(ambiguous_exact ..).mpr n]
  | cons x xs ih =>
    obtain ⟨v,here⟩ := earlier x List.mem_cons_self
    have tail := ih (fun k h => earlier k (List.mem_cons_of_mem _ h))
    simp [requireAll,here,tail,Except.map]

theorem first_failure (c : Catalog) (qs : List Query) (why : Issue) :
    requireAll c qs = .error why ↔ ∃ pre q rest, qs = pre ++ q::rest ∧
      Supported c pre ∧ Bad c q why := by
  constructor
  · intro h
    induction qs with
    | nil => cases h
    | cons q qs ih =>
      cases current : lookup c q with
      | unobserved =>
        have e : Issue.missing q = why := by simpa [requireAll,current] using h
        exact ⟨[],q,qs,rfl,by simp [Supported],e ▸ ⟨rfl,(empty_exact ..).mp current⟩⟩
      | ambiguous =>
        have e : Issue.ambiguous q = why := by simpa [requireAll,current] using h
        exact ⟨[],q,qs,rfl,by simp [Supported],e ▸ ⟨rfl,(ambiguous_exact ..).mp current⟩⟩
      | known v =>
        cases rest : requireAll c qs with
        | ok t => simp [requireAll,current,rest,Except.map] at h
        | error err =>
          have eq : err = why := by simpa [requireAll,current,rest,Except.map] using h
          obtain ⟨pre,k,after,place,passed,bad⟩ := ih (eq ▸ rest)
          refine ⟨q::pre,k,after,by simp [place],?_,bad⟩
          intro x here
          rcases List.mem_cons.mp here with rfl | later
          · exact ⟨_,current⟩
          · exact passed x later
  · rintro ⟨pre,q,rest,rfl,ready,reason⟩
    exact fails_at_prefix c pre rest q why ready reason

end Yulang.GeneralSourceRoleCstCatalogFailure296
