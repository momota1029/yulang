import Yulang.GeneralSourceRoleCstCatalogFootprint296

/-! A successful selected table determines precisely its own finite queried
catalog, not any additional names in the input provider. -/
namespace Yulang.GeneralSourceRoleCstTrimCatalog296
open GeneralSourceRoleCstNameCatalog296 (Catalog environment)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff)
open GeneralSourceRoleCstCatalogExport296 (run Exported run_exact)
open GeneralSourceRoleCstSelectedEvidence296 (extract_after_finite_export extracted_table_replays)
open GeneralSourceRoleCstCatalogTrace296 (produce_exact)
open GeneralSourceRoleCstCoalesce296 (coalesce coalesce_mem)
open GeneralSourceRoleCstRecoveredCatalog296 (catalog_releases_exact_capture)
open GeneralSourceRoleCstCatalogFootprint296 (trace_does_not_invent_row)
open GeneralSourceRoleCstTrackedRow296 (tracked_row_exact)
open GeneralSourceRoleCstReifyRow296 (recover_from_existing_lowerer)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

theorem trim_preserves_full_export {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (success : run policy scope w brand a sealed c fallback = .ok out) :
    run policy scope w brand a sealed (coalesce out.trace) fallback = .ok out ∧
      ∀ row ∈ coalesce out.trace, row ∈ c := by
  obtain ⟨p,r,site,shape,issued,attached⟩ := (run_exact ..).mp success
  have inverse := extract_after_finite_export policy scope w brand a sealed c fallback out success
  obtain ⟨t,replayed⟩ := extracted_table_replays policy scope w brand a sealed out.table (coalesce out.trace) inverse
  have arity := ((tracked_row_exact ..).mp attached)
  obtain ⟨_,_,_,_,eq,_,_⟩ := arity
  rw [eq] at replayed
  obtain ⟨p',r',site',shape',produced,back⟩ := (run_exact ..).mp replayed
  cases Option.some.inj (site'.symm.trans site)
  cases Option.some.inj (shape'.symm.trans shape)
  have trace := ((produce_exact ..).mp issued).2
  have original := catalog_releases_exact_capture (environment c) r.role
  rw [trace] at original
  have eqTrace := Except.ok.inj (produced.symm.trans original)
  refine ⟨(run_exact ..).mpr ⟨p,r,site,shape,eqTrace ▸ produced,back⟩,?_⟩
  rintro ⟨q,v⟩ member
  exact trace_does_not_invent_row c _ _ issued q v ((coalesce_mem ..).mp member)

theorem selected_table_determines_trace {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c d : Catalog) (fallback : Nat) (out other : Exported)
    (first : run policy scope w brand a sealed c fallback = .ok out)
    (second : run policy scope w brand a sealed d fallback = .ok other)
    (same : out.table = other.table) : out.trace = other.trace := by
  obtain ⟨p,r,site,shape,issued,attached⟩ := (run_exact ..).mp first
  obtain ⟨p',r',site',shape',issued',attached'⟩ := (run_exact ..).mp second
  cases Option.some.inj (site'.symm.trans site)
  cases Option.some.inj (shape'.symm.trans shape)
  obtain ⟨sym,row,seen,rows,_,_,lowered⟩ := (tracked_row_exact ..).mp attached
  obtain ⟨sym',row',seen',rows',_,_,lowered'⟩ := (tracked_row_exact ..).mp attached'
  cases Option.some.inj (seen.symm.trans shape)
  cases Option.some.inj (seen'.symm.trans shape)
  have sameRow : row = row' := List.mem_singleton.mp (show row ∈ [row'] by
    rw [← rows',← same,rows]; exact List.mem_cons_self)
  subst row'
  have e := recover_from_existing_lowerer lowered
  have e' := recover_from_existing_lowerer lowered'
  rw [((produce_exact ..).mp issued).2] at e
  rw [((produce_exact ..).mp issued').2] at e'
  exact Option.some.inj (e.symm.trans e')

end Yulang.GeneralSourceRoleCstTrimCatalog296
