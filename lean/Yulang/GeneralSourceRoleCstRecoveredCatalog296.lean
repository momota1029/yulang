import Yulang.GeneralSourceRoleCstCoalesce296

/-! Checked inversion of a supported resolved row. Contradictory recovered
observations cannot be released as a successful finite catalog. -/
namespace Yulang.GeneralSourceRoleCstRecoveredCatalog296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup environment known_exact known_reply)
open GeneralSourceRoleCstCatalogTrace296 (produce produce_exact Supported)
open GeneralSourceRoleCstCoalesce296 (coalesce coalesce_mem coalesce_nodup singleton_fiber)
open GeneralSourceRoleCstNamingRequests295 (Query queryList reply SameReplies query_role_exact)
open GeneralSourceRoleCstNamingTrace295 (Trace values capture query_shape captures_eq_agree)
open GeneralSourceRoleCstReifyRow296 (recover recover_from_existing_lowerer recover_replays)
open GeneralSourceRoleCstReifyBody296 (Matches values_match)
open GeneralSourceRoleSpelling292 (Environment Role)
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceRoleExport292 (resolveRole)

theorem captured_key_known (e : Environment) (r : Role) (q : Query)
    (read : q ∈ queryList e r) : lookup (coalesce (capture e r)) q = .known (reply e q) := by
  have appears : (q,reply e q) ∈ capture e r := List.mem_map.mpr ⟨q,read,rfl⟩
  apply (known_exact ..).mpr
  apply singleton_fiber _ q (reply e q) (coalesce_nodup _)
  · exact (coalesce_mem ..).mpr appears
  · intro v taken
    exact (values_match e _ (q,v) ((coalesce_mem ..).mp taken)).symm

theorem catalog_releases_exact_capture (e : Environment) (r : Role) :
    produce (coalesce (capture e r)) r = .ok (capture e r) := by
  let c := coalesce (capture e r)
  have same : SameReplies e (environment c) (queryList e r) := by
    intro q mem
    exact (known_reply c q (reply e q) (captured_key_known e r q mem)).symm
  have agree := (query_role_exact ..).mp same
  have equivalent := query_shape r agree
  have known : Supported c (queryList (environment c) r) := by
    rw [←equivalent]
    exact fun q h => ⟨reply e q,captured_key_known e r q h⟩
  exact (produce_exact ..).mpr ⟨known,((captures_eq_agree ..).mpr agree).symm⟩

def recoverCatalog (r : Role) (row : BareRow) : Option Catalog :=
  (recover r row).bind fun t =>
    let c := coalesce t
    match produce c r with
    | .error _ => none
    | .ok got => if got = t then some c else none

theorem recover_catalog_exact (r : Role) (row : BareRow) (c : Catalog) :
    recoverCatalog r row = some c ↔
      ∃ t, recover r row = some t ∧ c = coalesce t ∧ produce c r = .ok t := by
  constructor
  · intro h
    cases decoded : recover r row with
    | none => simp [recoverCatalog,decoded] at h
    | some t =>
      cases ready : produce (coalesce t) r with
      | error why => simp [recoverCatalog,decoded,ready] at h
      | ok rows =>
        by_cases kept : rows = t
        · subst rows
          have e : coalesce t = c := by simpa [recoverCatalog,decoded,ready] using h
          exact ⟨t,rfl,e.symm,e ▸ ready⟩
        · simp [recoverCatalog,decoded,ready,kept] at h
  · rintro ⟨t,decoded,rfl,pass⟩
    simp [recoverCatalog,decoded,pass]

theorem inverted_from_lowered {e : Environment} {r : Role} {row : BareRow}
    (lowered : resolveRole e r = some row) :
    recoverCatalog r row = some (coalesce (capture e r)) := by
  simp [recoverCatalog,recover_from_existing_lowerer lowered,catalog_releases_exact_capture]

theorem recovered_catalog_relowers {r : Role} {row : BareRow} {c : Catalog}
    (evidence : recoverCatalog r row = some c) :
    resolveRole (environment c) r = some row := by
  obtain ⟨t,raw,_,actual⟩ := (recover_catalog_exact ..).mp evidence
  have exactTrace := ((produce_exact ..).mp actual).2
  have fits : Matches (environment c) t := exactTrace ▸ values_match (environment c) (queryList (environment c) r)
  exact recover_replays raw fits

end Yulang.GeneralSourceRoleCstRecoveredCatalog296
