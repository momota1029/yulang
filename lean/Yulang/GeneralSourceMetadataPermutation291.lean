import Yulang.GeneralSourceMetadataTransportFixture291

/-! With unique resolved keys, finite source semantics is independent of
the input list order. The proof preserves the old projected functions. -/
namespace Yulang.GeneralSourceMetadataPermutation291
open GeneralSourceMetadataFiniteLookup291 (get some_sound some_complete)
open GeneralObservedMetadataOverlay290 (overlay)
open GeneralSourceMetadataRows291
open GeneralSourceMetadataValidation291 (Valid)

theorem get_perm {α : Type} {a b : List (Nat × α)}
    (perm : a.Perm b) (unique : (a.map Prod.fst).Nodup) (k : Nat) :
    get k a = get k b := by
  have other := (perm.map Prod.fst).nodup unique
  cases known : get k a with
  | some record =>
    exact (some_complete other (perm.mem_iff.mp (some_sound known))).symm
  | none =>
    cases found : get k b with
    | none => rfl
    | some record =>
      have orig := some_complete unique (perm.mem_iff.mpr (some_sound found))
      rw [known] at orig
      cases orig

theorem overlay_get {α : Type} (fallback : Nat → α) (rows : List (Nat × α)) (k : Nat) :
    overlay fallback rows k = (get k rows).getD (fallback k) := by
  induction rows with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨n,value⟩
    by_cases seen : k = n
    · simp [overlay,GeneralSourceMetadataFiniteLookup291.get,seen]
    · simpa [overlay,GeneralSourceMetadataFiniteLookup291.get,seen] using ih

theorem table_perm {α : Type} {a b : List (Nat × α)} (fallback : Nat → α)
    (perm : a.Perm b) (unique : (a.map Prod.fst).Nodup) :
    overlay fallback a = overlay fallback b := by
  funext k
  rw [overlay_get,overlay_get,get_perm perm unique]

theorem projected_perm {s t : Source} (ordered : s.rows.Perm t.rows)
    (unique : (s.rows.map Row.key).Nodup) (f : Row → α) (fallback : Nat → α) :
    overlay fallback (s.rows.map (fun row => (row.key,f row))) =
      overlay fallback (t.rows.map (fun row => (row.key,f row))) := by
  apply table_perm fallback (ordered.map _)
  simpa only [List.map_map,Function.comp_def] using unique

theorem source_perm {s t : Source} (ordered : s.rows.Perm t.rows)
    (shared : s.fallback = t.fallback) (good : Valid s) :
    Valid t ∧ constructors s = constructors t ∧ interpretation s = interpretation t := by
  refine ⟨⟨(ordered.map Row.key).nodup good.1,fun row member => good.2 row (ordered.mem_iff.mpr member)⟩,?_,?_⟩
  · unfold constructors constructorRows
    rw [← shared]
    exact projected_perm ordered good.1 Row.ctor s.fallback.decode
  · apply interpretation_ext
    · exact projected_perm ordered good.1 (fun r => r.classification.primitiveValue) (fun _ => none)
    · exact projected_perm ordered good.1 (fun r => r.classification.invariantFlag) (fun _ => false)

end Yulang.GeneralSourceMetadataPermutation291
