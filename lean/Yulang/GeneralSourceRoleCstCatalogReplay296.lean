import Yulang.GeneralSourceRoleCstCatalogExport296

/-! A successful finite output replays against any independently supplied
environment that has exactly the demanded observations at the selected scope. -/
namespace Yulang.GeneralSourceRoleCstCatalogReplay296
open GeneralSourceRoleCstNameCatalog296 (Catalog environment)
open GeneralSourceRoleCstCatalogAgreement296 (Fits producer_trace_authority supported_role_exact)
open GeneralSourceRoleCstCatalogTrace296 (produce_exact)
open GeneralSourceRoleCstCatalogExport296 (Exported run run_exact)
open GeneralSourceRoleCstNamingRequests295 (queryList)
open GeneralSourceRoleCstNamingScope295 (symbolic compile_env_congr)
open GeneralSourceRoleCstNamingPacket295 (checked capture_at_exact checked_exact)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile handoff)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleSpelling292 (Environment)

theorem agrees_replays {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat)
    (out : Exported) (built : run policy scope w brand a sealed c fallback = .ok out)
    (reference : S → Environment) :
    ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
      (Fits c (queryList (environment c) r.role) (reference r.scope) ↔
        checked policy scope w brand a ⟨sealed,out.trace⟩ reference fallback = some out.table) := by
  obtain ⟨p,r,found,shape,issued,lowered⟩ := (run_exact ..).mp built
  refine ⟨p,r,found,shape,?_⟩
  have covered := ((produce_exact ..).mp issued).1
  have trace := producer_trace_authority issued (reference r.scope)
  constructor
  · intro fits
    have eq : compile policy scope w brand a sealed (fun _ => environment c) fallback =
        compile policy scope w brand a sealed reference fallback := by
      apply compile_env_congr
      intro p' picked r' parsed
      cases Option.some.inj (picked.symm.trans found)
      cases Option.some.inj (parsed.symm.trans shape)
      exact (supported_role_exact _ _ _ covered).mp fits
    have outOld : compile policy scope w brand a sealed (fun _ => environment c) fallback =
        some out.table := by simp [compile,found,lowered]
    exact (checked_exact ..).mpr
      ⟨(capture_at_exact ..).mpr ⟨p,r,found,shape,trace.mp fits⟩,eq.symm ▸ outOld⟩
  · intro replay
    obtain ⟨captured,_⟩ := (checked_exact ..).mp replay
    obtain ⟨p',r',picked,parsed,steps⟩ := (capture_at_exact ..).mp captured
    cases Option.some.inj (picked.symm.trans found)
    cases Option.some.inj (parsed.symm.trans shape)
    exact trace.mpr steps

end Yulang.GeneralSourceRoleCstCatalogReplay296
