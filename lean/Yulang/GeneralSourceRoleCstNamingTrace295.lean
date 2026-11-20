import Yulang.GeneralSourceRoleCstNamingRequests295

/-! The ordered list is a finite exportable attestation of lookup values.
Equality verifies completeness relative to a reference role, not trust. -/
namespace Yulang.GeneralSourceRoleCstNamingTrace295
open GeneralSourceRoleSpelling292 (Environment Role Output)
open GeneralSourceRoleLocalEnv292 (Agree OutputAgree)
open GeneralSourceRoleCstNamingRequests295
  (Query reply queryList outputQueries bodyQueries SameReplies query_role_exact same_replies_cons)

abbrev Trace := List (Query × Option Nat)

def values (e : Environment) (qs : List Query) : Trace :=
  qs.map (fun q => (q,reply e q))

def capture (e : Environment) (r : Role) : Trace :=
  values e (queryList e r)

theorem values_keys (e : Environment) (qs : List Query) :
    (values e qs).map Prod.fst = qs := by
  simp [values,List.map_map,Function.comp_def]

theorem values_agree_exact (e f : Environment) (qs : List Query) :
    values e qs = values f qs ↔ SameReplies e f qs := by
  induction qs with
  | nil => simp [values,SameReplies]
  | cons q qs ih =>
    rw [same_replies_cons,←ih]
    unfold values
    simp only [List.map_cons,List.cons.injEq,Prod.mk.injEq,true_and]

theorem output_query_shape {e f : Environment} (id : Nat) (o : Output)
    (h : OutputAgree e f id o) : outputQueries e id o = outputQueries f id o := by
  simp [outputQueries,h.1]

theorem flat_map_eq {A B : Type} (f g : A → List B) (xs : List A)
    (ok : ∀ a ∈ xs, f a = g a) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,List.flatMap_cons,ok x List.mem_cons_self,
      ih (fun a h => ok a (List.mem_cons_of_mem _ h))]

theorem query_shape {e f : Environment} (r : Role) (ok : Agree e f r) :
    queryList e r = queryList f r := by
  cases h : e.role r.spelling with
  | none => simp [queryList,h,ok.1.symm.trans h]
  | some id =>
    have hf := ok.1.symm.trans h
    rw [queryList,queryList,h,hf]
    congr 1
    apply flat_map_eq
    intro o m
    exact output_query_shape id o (ok.2 id h o m)

theorem captures_eq_agree (e f : Environment) (r : Role) :
    capture e r = capture f r ↔ Agree e f r := by
  constructor
  · intro h
    have keys : queryList e r = queryList f r := by
      simpa only [capture,values_keys] using congrArg (List.map Prod.fst) h
    have same : values e (queryList e r) = values f (queryList e r) := by
      simpa only [capture,← keys] using h
    exact (query_role_exact ..).mp ((values_agree_exact ..).mp same)
  · intro h
    have eq := (values_agree_exact ..).mpr ((query_role_exact ..).mpr h)
    simpa only [capture,←query_shape r h] using eq

end Yulang.GeneralSourceRoleCstNamingTrace295
