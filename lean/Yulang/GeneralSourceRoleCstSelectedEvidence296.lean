import Yulang.GeneralSourceRoleCstTableEvidence296

/-! Round-trip an accepted one-role old table through finite observed evidence
at the same selected scope and source path. -/
namespace Yulang.GeneralSourceRoleCstSelectedEvidence296
open GeneralSourceRoleCstNameCatalog296 (Catalog environment)
open GeneralSourceRoleCstTableEvidence296 (fromTable actual_table_inverts table_replays)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile handoff)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstNamingTrace295 (capture)
open GeneralSourceRoleCstCatalogTrace296 (produce_exact)
open GeneralSourceRoleCstCatalogExport296 (run Exported run_exact)
open GeneralSourceRoleCstCoalesce296 (coalesce)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceMetadataExprDomain291 (bind_success)

def extractCatalog {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (table : RoleSource) : Option Catalog :=
  (handoff policy scope w brand a sealed).bind (fun payload => fromTable payload table)

theorem selected_old_table_inverts {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (env : S → Environment) (fallback : Nat) (table : RoleSource)
    (old : compile policy scope w brand a sealed env fallback = some table) :
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      extractCatalog policy scope w brand a sealed table = some (coalesce (capture (env r.scope) r.role)) := by
  obtain ⟨p,picked,attached⟩ := bind_success old
  obtain ⟨r,shape,inverted⟩ := actual_table_inverts env fallback p table attached
  exact ⟨p,r,picked,shape,by simp [extractCatalog,picked,inverted]⟩

theorem extracted_table_replays {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (table : RoleSource) (c : Catalog)
    (obtained : extractCatalog policy scope w brand a sealed table = some c) :
    ∃ t, run policy scope w brand a sealed c table.fallbackArity = .ok ⟨t,table⟩ := by
  obtain ⟨p,picked,recovered⟩ := bind_success obtained
  obtain ⟨r,t,shape,issued,back⟩ := table_replays p table c recovered
  exact ⟨t,(run_exact ..).mpr ⟨p,r,picked,shape,issued,back⟩⟩

theorem extract_after_finite_export {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported)
    (success : run policy scope w brand a sealed c fallback = .ok out) :
    extractCatalog policy scope w brand a sealed out.table = some (coalesce out.trace) := by
  obtain ⟨p,r,picked,shape,produced,attached⟩ := (run_exact ..).mp success
  obtain ⟨s,symbol,back⟩ := actual_table_inverts (fun _ => environment c) fallback p out.table attached
  cases Option.some.inj (symbol.symm.trans shape)
  rw [((produce_exact ..).mp produced).2] at back
  simp [extractCatalog,picked,back]

end Yulang.GeneralSourceRoleCstSelectedEvidence296
