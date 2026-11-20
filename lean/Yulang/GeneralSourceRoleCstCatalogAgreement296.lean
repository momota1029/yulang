import Yulang.GeneralSourceRoleCstCatalogTrace296

/-! The catalog has exactly the effect of any name environment agreeing
on its observed required keys; this is not a theorem about hidden names. -/
namespace Yulang.GeneralSourceRoleCstCatalogAgreement296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup environment known_reply)
open GeneralSourceRoleCstCatalogTrace296 (Supported produce produce_exact)
open GeneralSourceRoleCstNamingRequests295 (Query queryList reply SameReplies query_role_exact)
open GeneralSourceRoleCstNamingTrace295 (Trace capture captures_eq_agree query_shape)
open GeneralSourceRoleSpelling292 (Environment Role)
open GeneralSourceRoleLocalEnv292 (Agree)

def Fits (c : Catalog) (qs : List Query) (e : Environment) : Prop :=
  ∀ q ∈ qs, ∀ v, lookup c q = .known v → reply e q = v

theorem own_environment_fits (c : Catalog) (qs : List Query) :
    Fits c qs (environment c) := by
  intro q _ v seen; exact known_reply c q v seen

theorem fits_iff_reads_agree (c : Catalog) (qs : List Query) (e : Environment)
    (complete : Supported c qs) :
    Fits c qs e ↔ SameReplies (environment c) e qs := by
  constructor
  · intro h q m
    obtain ⟨v,look⟩ := complete q m
    exact (known_reply c q v look).trans (h q m v look).symm
  · intro both q m v seen
    exact (both q m).symm.trans (known_reply c q v seen)

theorem supported_role_exact (c : Catalog) (r : Role) (e : Environment)
    (complete : Supported c (queryList (environment c) r)) :
    Fits c (queryList (environment c) r) e ↔ Agree (environment c) e r :=
  (fits_iff_reads_agree c _ e complete).trans (query_role_exact ..)

theorem producer_trace_authority {c : Catalog} {r : Role} {t : Trace}
    (issued : produce c r = .ok t) (e : Environment) :
    Fits c (queryList (environment c) r) e ↔ capture e r = t := by
  obtain ⟨covered,stamp⟩ := (produce_exact ..).mp issued
  rw [supported_role_exact c r e covered,← captures_eq_agree,stamp,eq_comm]

theorem queried_keys_stable {c : Catalog} {r : Role} {t : Trace}
    (issued : produce c r = .ok t) (e : Environment)
    (fits : Fits c (queryList (environment c) r) e) :
    queryList (environment c) r = queryList e r := by
  have supported := ((produce_exact ..).mp issued).1
  exact query_shape r ((supported_role_exact c r e supported).mp fits)

end Yulang.GeneralSourceRoleCstCatalogAgreement296
