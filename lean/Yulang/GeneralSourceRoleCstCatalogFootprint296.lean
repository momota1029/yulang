import Yulang.GeneralSourceRoleCstSelectedEvidence296

/-! Exact footprint of a successful finite observation: every trace row is
a literal input observation, with only repeated occurrences coalesced. -/
namespace Yulang.GeneralSourceRoleCstCatalogFootprint296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup environment fiber known_reply known_exact member_of_fiber)
open GeneralSourceRoleCstNamingRequests295 (Query queryList reply)
open GeneralSourceRoleCstNamingTrace295 (Trace values)
open GeneralSourceRoleCstCatalogTrace296 (produce produce_exact)
open GeneralSourceRoleCstCoalesce296 (coalesce coalesce_mem)
open GeneralSourceRoleSpelling292 (Role)

theorem produced_member_exact (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) :
    (q,v) ∈ t ↔ q ∈ queryList (environment c) r ∧ lookup c q = .known v := by
  obtain ⟨known,capture⟩ := (produce_exact ..).mp made
  subst t
  change (q,v) ∈ values (environment c) (queryList (environment c) r) ↔ _
  constructor
  · intro hit
    obtain ⟨k,m,e⟩ := List.mem_map.mp hit
    have same := Prod.mk.inj e
    rcases same with ⟨rfl,value⟩
    obtain ⟨out,one⟩ := known _ m
    exact ⟨m,(value ▸ known_reply c k out one) ▸ one⟩
  · rintro ⟨read,one⟩
    exact List.mem_map.mpr ⟨q,read,Prod.ext rfl (known_reply c q v one)⟩

theorem trace_does_not_invent_row (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) (entry : (q,v) ∈ t) :
    (q,v) ∈ c := by
  have only := ((produced_member_exact c r t made q v).mp entry).2
  apply (member_of_fiber ..).mp
  rw [(known_exact ..).mp only]
  exact List.mem_cons_self

theorem coalesced_footprint_exact (c : Catalog) (r : Role) (t : Trace)
    (made : produce c r = .ok t) (q : Query) (v : Option Nat) :
    (q,v) ∈ coalesce t ↔ q ∈ queryList (environment c) r ∧ lookup c q = .known v :=
  (coalesce_mem ..).trans (produced_member_exact c r t made q v)

end Yulang.GeneralSourceRoleCstCatalogFootprint296
