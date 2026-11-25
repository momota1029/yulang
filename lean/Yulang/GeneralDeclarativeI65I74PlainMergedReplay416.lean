import Yulang.GeneralDeclarativeI65I74PlainMergedRule416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (point)
open ClosedResidual415 (readCandidate415)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure PlainWire where
  origin : Nat
  variantRow : Nat
  intRow : Nat
  joinRow : Nat
  declaration : Nat
  rootEscape : ExactEscapeWire

def readRows416 (p : Problem) (w : PlainWire) : Option (PlainRows p.state p.root) := do
  let s := p.state.core
  let rows := s.current.ordinary.equations
  match found : s.origins[w.origin]? with
  | some original =>
    match term : original.endpoint with
    | .ordinary (.variant tag (.var payload)) =>
      match args : p.root.demand.arguments with
      | [arg] =>
        if own : arg.lower = original.slot ∧ arg.center = original.slot ∧
            arg.upper = original.slot ∧ p.root.demand.outputs = [] then
          if exact : original.slot ≠ payload ∧
              (s.origins.filter (fun src => src.slot == original.slot)).length = 1 ∧
              rows[w.variantRow]? = some (variantRow416 original.slot tag payload) ∧
              rows.filter (variantPayload original.slot tag) = [variantRow416 original.slot tag payload] ∧
              rows[w.intRow]? = some (OpenTail414.intRow payload) ∧
              rows[w.joinRow]? = some (idempotentRow original.slot) then
            have argExact : arg = point original.slot := by
              cases arg
              simp only [point]
              congr
              · exact own.1
              · exact own.2.1
              · exact own.2.2.1
            some ⟨original.slot,tag,payload,exact.1,
              args.trans (congrArg (fun c => [c]) argExact),own.2.2.2,
              original,List.mem_of_getElem? found,rfl,exact.2.1,term,
              List.mem_of_getElem? exact.2.2.1,exact.2.2.2.1,
              List.mem_of_getElem? exact.2.2.2.2.1,List.mem_of_getElem? exact.2.2.2.2.2⟩
          else none
        else none
      | _ => none
    | _ => none
  | none => none

def readPlainHead416 {s q} (a : PlainRows s q) (ordinal : Nat) : Option (PlainRead a) := do
  let row ← readCandidate415 s q ordinal
  if noWhere : row.decl.requirements = [] then
    match literal : row.decl.head with
    | [.join (.variant tag₁ (.var binder₁)) (.variant tag₂ (.var binder₂))] =>
      if same : tag₁ = a.tag ∧ tag₂ = a.tag ∧ binder₁ ≠ binder₂ then
        some ⟨row,binder₁,binder₂,same.2.2,by simpa [sourceX6,same.1,same.2.1] using literal,noWhere⟩
      else none
    | _ => none
  else none

structure VerifiedPlain (p : Problem) where
  rows : PlainRows p.state p.root
  actual : PlainRead rows
  rootSafe : ¬ RootCycle p.state p.root

def replayPlain416 (p : Problem) (w : PlainWire) : Option (VerifiedPlain p) := do
  let a ← readRows416 p w
  if escape : checkExactEscape p.state.core.current.ordinary a.root w.rootEscape = true then
    let head ← readPlainHead416 a w.declaration
    have safe : ¬ RootCycle p.state p.root := by
      rintro ⟨x,atRoot,cycle⟩
      rw [a.requested] at atRoot
      cases List.mem_singleton.mp atRoot
      exact exact_escape_refutes_raw_root_K2410 escape cycle
    some ⟨a,head,safe⟩
  else none

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
