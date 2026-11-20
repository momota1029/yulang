import Yulang.GeneralSourceRoleCstNameCatalog296

/-! Produce the ordered C295 trace only if each requested lookup was
observed exactly once. Duplicate query occurrences in the program may
reuse the same single observation. -/
namespace Yulang.GeneralSourceRoleCstCatalogTrace296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup fiber lookup environment known_reply)
open GeneralSourceRoleCstNamingRequests295 (Query queryList)
open GeneralSourceRoleCstNamingTrace295 (Trace values capture)
open GeneralSourceRoleSpelling292 (Role)

inductive Issue where
  | missing (q : Query)
  | ambiguous (q : Query)
  deriving DecidableEq, Repr

def requireAll (c : Catalog) : List Query → Except Issue Trace
  | [] => .ok []
  | q::qs =>
    match lookup c q with
    | .unobserved => .error (.missing q)
    | .ambiguous => .error (.ambiguous q)
    | .known v => (requireAll c qs).map ((q,v)::·)

def Supported (c : Catalog) (qs : List Query) : Prop :=
  ∀ q ∈ qs, ∃ v, lookup c q = .known v

theorem require_exact (c : Catalog) (qs : List Query) (tr : Trace) :
    requireAll c qs = .ok tr ↔ Supported c qs ∧ values (environment c) qs = tr := by
  induction qs generalizing tr with
  | nil => simp [requireAll,Supported,values,eq_comm]
  | cons q qs ih =>
    cases h : lookup c q with
    | unobserved =>
      simp only [requireAll,h,reduceCtorEq,false_iff]
      intro supp
      obtain ⟨_,bad⟩ := supp.1 q List.mem_cons_self
      simp [h] at bad
    | ambiguous =>
      simp only [requireAll,h,reduceCtorEq,false_iff]
      intro supp
      obtain ⟨_,bad⟩ := supp.1 q List.mem_cons_self
      simp [h] at bad
    | known v =>
      have supp : Supported c (q::qs) ↔ Supported c qs := by
        constructor
        · exact fun ok a mem => ok a (List.mem_cons_of_mem _ mem)
        · intro ok a mem
          rcases List.mem_cons.mp mem with rfl | rest
          · exact ⟨v,h⟩
          · exact ok a rest
      rw [supp]
      cases step : requireAll c qs with
      | error why =>
        constructor
        · simp [requireAll,h,step,Except.map]
        · intro ⟨supported,_⟩
          have ok := (ih _).mpr ⟨supported,rfl⟩
          rw [step] at ok
          cases ok
      | ok tail =>
        obtain ⟨supported,rfl⟩ := (ih ..).mp step
        simp [requireAll,h,step,supported,Except.map,values,known_reply c q v h]

def produce (c : Catalog) (r : Role) : Except Issue Trace :=
  requireAll c (queryList (environment c) r)

theorem produce_exact (c : Catalog) (r : Role) (tr : Trace) :
    produce c r = .ok tr ↔ Supported c (queryList (environment c) r) ∧
      capture (environment c) r = tr :=
  require_exact ..

end Yulang.GeneralSourceRoleCstCatalogTrace296
