import Yulang.GeneralSourceRoleCstCatalogEntry296

/-! Incoming evidence is an ordered transport, not first-wins lookup.
Validation preserves output query order and ignores input-row permutation. -/
namespace Yulang.GeneralSourceRoleCstCatalogOrder296
open GeneralSourceRoleCstNameCatalog296
  (Catalog Lookup lookup fiber known_exact empty_exact ambiguous_exact provisional environment reply_from_catalog)
open GeneralSourceRoleCstCatalogTrace296 (requireAll produce)
open GeneralSourceRoleCstNamingRequests295 (Query queryList SameReplies query_role_exact)
open GeneralSourceRoleCstNamingTrace295 (query_shape)
open GeneralSourceRoleSpelling292 (Role)
open GeneralSourceRoleCstCatalogExport296 (run)
open GeneralSourceRoleCstNamingScope295 (symbolic tracked_env_congr)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)

theorem fiber_perm {c d : Catalog} (h : c.Perm d) (q : Query) :
    (fiber c q).Perm (fiber d q) :=
  (h.filter (fun (p : Query × Option Nat) => decide (p.1 = q))).map Prod.snd

theorem lookup_perm {c d : Catalog} (h : c.Perm d) (q : Query) :
    lookup c q = lookup d q := by
  have order := fiber_perm h q
  cases s : lookup c q with
  | unobserved =>
    have old := (empty_exact ..).mp s
    have reset : (fiber d q).Perm [] := old ▸ order.symm
    exact ((empty_exact ..).mpr reset.eq_nil).symm
  | known v =>
    have old := (known_exact ..).mp s
    have reset : (fiber d q).Perm [v] := old ▸ order.symm
    exact ((known_exact ..).mpr reset.eq_singleton).symm
  | ambiguous =>
    have old := (ambiguous_exact ..).mp s
    exact ((ambiguous_exact ..).mpr (order.length_eq ▸ old)).symm

theorem require_congr_on_keys {c d : Catalog} (qs : List Query)
    (same : ∀ q ∈ qs, lookup c q = lookup d q) :
    requireAll c qs = requireAll d qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have one := same q List.mem_cons_self
    have rest := ih (fun x h => same x (List.mem_cons_of_mem _ h))
    simp only [requireAll,one,rest]

theorem produce_local {c d : Catalog} (r : Role)
    (same : ∀ q ∈ queryList (environment c) r, lookup c q = lookup d q) :
    produce c r = produce d r := by
  have consistent : SameReplies (environment c) (environment d) (queryList (environment c) r) := by
    intro q m
    simp [reply_from_catalog,provisional,same q m]
  have shape := query_shape r ((query_role_exact ..).mp consistent)
  unfold produce
  rw [←shape]
  exact require_congr_on_keys _ same

theorem run_local {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat)
    (same : ∀ p r, handoff policy scope w brand a sealed = some p → symbolic p = some r →
      ∀ q ∈ queryList (environment c) r.role, lookup c q = lookup d q) :
    run policy scope w brand a sealed c fallback = run policy scope w brand a sealed d fallback := by
  cases h : handoff policy scope w brand a sealed with
  | none => simp [run,h]
  | some p =>
    cases s : symbolic p with
    | none => simp [run,h,s]
    | some r =>
      have onDemand := same p r h s
      have consistent : SameReplies (environment c) (environment d) (queryList (environment c) r.role) := by
        intro q m
        simp [reply_from_catalog,provisional,onDemand q m]
      have mapped := (query_role_exact ..).mp consistent
      have lowerEq : GeneralSourceRoleTrack292.runTracked (fun _ => environment c) fallback [p] =
        GeneralSourceRoleTrack292.runTracked (fun _ => environment d) fallback [p] := by
        apply tracked_env_congr
        intro v hv
        cases Option.some.inj (s.symm.trans hv)
        exact mapped
      simp [run,h,s,produce_local r.role onDemand,lowerEq]

theorem run_perm {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat) (same : c.Perm d) :
    run policy scope w brand a sealed c fallback = run policy scope w brand a sealed d fallback := by
  apply run_local
  intro _ _ _ _ q _
  exact lookup_perm same q

end Yulang.GeneralSourceRoleCstCatalogOrder296
