import Yulang.GeneralSourceRoleCstIssuedScope296

/-! Rescope a successful result as exact value evidence. The source wire is
retained, so minimizing catalog rows is not a claim to redact source text. -/
namespace Yulang.GeneralSourceRoleCstIssuePacket296
open GeneralSourceRoleCstIssuedScope296 (Packet accept accept_exact checks_exact)
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstCatalogExport296 (Exported Failure run)
open GeneralSourceRoleCstCoalesce296 (coalesce)
open GeneralSourceRoleCstTrimCatalog296 (trim_preserves_full_export)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

structure Issued (S B R : Type) where
  packet : Packet S B R
  exportResult : Exported

def issue {S B R : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (epoch : R) (sealed : Boundary S B) (c : Catalog) (fallback : Nat) : Except Failure (Issued S B R) :=
  (run policy scope w brand a sealed c fallback).map fun x =>
    ⟨⟨w,scope,a,policy,epoch,fallback,coalesce x.trace⟩,x⟩

theorem issue_exact {S B R : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (epoch : R) (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Issued S B R) :
    issue policy scope w brand a epoch sealed c fallback = .ok out ↔
      run policy scope w brand a sealed c fallback = .ok out.exportResult ∧
      out.packet = ⟨w,scope,a,policy,epoch,fallback,coalesce out.exportResult.trace⟩ := by
  cases out with
  | mk packet old =>
    cases h : run policy scope w brand a sealed c fallback with
    | error e => simp [issue,h,Except.map]
    | ok x =>
      simp [issue,h,Except.map,Issued.mk.injEq]
      constructor
      · rintro ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩
      · rintro ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩

theorem issued_replays_exact {S B R : Type} [DecidableEq S] [DecidableEq B] [DecidableEq R]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (epoch : R) (sealed : Boundary S B) (c : Catalog) (fallback : Nat) (out : Issued S B R)
    (ready : issue policy scope w brand a epoch sealed c fallback = .ok out) :
    accept out.packet w scope brand a policy epoch sealed fallback = .ok out.exportResult ∧
      (∀ row ∈ out.packet.catalog, row ∈ c) := by
  obtain ⟨lowered,packet⟩ := (issue_exact ..).mp ready
  obtain ⟨replay,subset⟩ :=
    trim_preserves_full_export policy scope w brand a sealed c fallback out.exportResult lowered
  rw [packet]
  exact ⟨(accept_exact ..).mpr ⟨(checks_exact ..).mpr ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,replay⟩,subset⟩

end Yulang.GeneralSourceRoleCstIssuePacket296
