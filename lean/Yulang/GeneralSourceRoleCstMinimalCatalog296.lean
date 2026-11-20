import Yulang.GeneralSourceRoleCstIssueControl296

/-! Least observed footprint amongst successful producers for the same
given selected table; this is not absolute semantic authority. -/
namespace Yulang.GeneralSourceRoleCstMinimalCatalog296
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstCoalesce296 (coalesce coalesce_nodup)
open GeneralSourceRoleCstTrimCatalog296 (trim_preserves_full_export selected_table_determines_trace)
open GeneralSourceRoleCstCatalogExport296 (Exported run)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

theorem coalesce_preserves_unique (t : Trace) (unique : t.Nodup) : coalesce t = t := by
  induction t with
  | nil => rfl
  | cons a ts ih =>
    have ⟨fresh,remaining⟩ := List.nodup_cons.mp unique
    simp [coalesce,fresh,ih remaining]

theorem coalesce_idempotent (t : Trace) : coalesce (coalesce t) = coalesce t :=
  coalesce_preserves_unique _ (coalesce_nodup _)

theorem least_among_same_selected_table {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (bound : Boundary S B) (c d : Catalog) (fallback : Nat) (out other : Exported)
    (first : run policy scope w brand a bound c fallback = .ok out)
    (second : run policy scope w brand a bound d fallback = .ok other)
    (same : out.table = other.table) :
    ∀ row ∈ coalesce out.trace, row ∈ d := by
  have coincides := selected_table_determines_trace policy scope w brand a bound c d fallback
    out other first second same
  rw [coincides]
  exact (trim_preserves_full_export policy scope w brand a bound d fallback other second).2

end Yulang.GeneralSourceRoleCstMinimalCatalog296
