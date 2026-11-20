import Yulang.GeneralSourceRoleCstCatalogAgreement296

/-! Closed finite producer/consumer: no total name map is requested.
The old role exporter is still the only component that creates rows. -/
namespace Yulang.GeneralSourceRoleCstCatalogExport296
open GeneralSourceRoleCstNameCatalog296 (Catalog environment)
open GeneralSourceRoleCstCatalogTrace296 (Issue produce)
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)
open GeneralSourceRoleTrack292 (runTracked)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceMetadataRoles291 (RoleSource)

inductive Failure where
  | selection
  | symbolic
  | evidence (reason : Issue)
  | oldExport
  deriving DecidableEq, Repr

structure Exported where
  trace : Trace
  table : RoleSource

def run {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) : Except Failure Exported :=
  match handoff policy scope w brand a sealed with
  | none => .error .selection
  | some p => match symbolic p with
    | none => .error .symbolic
    | some r => match produce c r.role with
      | .error e => .error (.evidence e)
      | .ok t => match runTracked (fun _ => environment c) fallback [p] with
        | none => .error .oldExport
        | some out => .ok ⟨t,out⟩

theorem run_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Exported) :
    run policy scope w brand a sealed c fallback = .ok out ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        produce c r.role = .ok out.trace ∧
        runTracked (fun _ => environment c) fallback [p] = some out.table := by
  cases out with
  | mk trace table =>
    cases h : handoff policy scope w brand a sealed with
    | none => simp [run,h]
    | some pick =>
      cases r : symbolic pick with
      | none => simp [run,h,r]
      | some sym =>
        cases seen : produce c sym.role with
        | error why => simp [run,h,r,seen]
        | ok rows =>
          cases built : runTracked (fun _ => environment c) fallback [pick] with
          | none => simp [run,h,r,seen,built]
          | some tab => simp [run,h,r,seen,built,Exported.mk.injEq]

theorem evidence_failure_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (why : Issue) :
    run policy scope w brand a sealed c fallback = .error (.evidence why) ↔
      ∃ p r, handoff policy scope w brand a sealed = some p ∧ symbolic p = some r ∧
        produce c r.role = .error why := by
  cases h : handoff policy scope w brand a sealed with
  | none => simp [run,h]
  | some pick =>
    cases r : symbolic pick with
    | none => simp [run,h,r]
    | some s =>
      cases seen : produce c s.role with
      | error e => simp [run,h,r,seen]
      | ok tr => cases built : runTracked (fun _ => environment c) fallback [pick] <;>
          simp [run,h,r,seen,built]

end Yulang.GeneralSourceRoleCstCatalogExport296
