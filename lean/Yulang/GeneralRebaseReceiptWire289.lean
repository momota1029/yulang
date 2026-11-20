import Yulang.GeneralRebaseRowDeferredDecisionGuard288

/-! Finite provenance interface for the auxiliary receipt driver.
This checks structured claims, not the validity of arbitrary raw journals. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReceiptWire289
open GeneralDeclarations (Declaration)

structure Offer where
  world : List Declaration
  parent : Nat
  parentKey : Nat
  child : Nat
  childKey : Nat
  output : Nat
  deriving Repr, DecidableEq

structure Producer where
  world : List Declaration
  parent : Nat
  parentKey : Nat
  children : List Nat
  targets : List Nat
  deriving Repr, DecidableEq

def Producer.matches (p : Producer) (ask : Offer) : Bool :=
  decide (p.world = ask.world ∧ p.parent = ask.parent ∧ p.parentKey = ask.parentKey ∧
    ask.child ∈ p.children ∧ ask.output ∈ p.targets)

structure Inspection where
  blocked : Bool
  conflicts : Bool
  arity : Bool
  deriving Repr, DecidableEq

def Inspection.finished (p : Inspection) : Bool :=
  !p.blocked && !p.conflicts && !p.arity

structure Wire where
  world : List Declaration
  producers : List Producer
  edges : List (Nat × Nat)
  child : Nat
  candidates : List Declaration
  childTargets : List Nat
  rootHasNominal : Bool
  inspect : Option Inspection
  deriving Repr

inductive Decision where
  | wrongWorld | missingProducer | detached | notUnique | nonInert | unobserved | unfinished | ready
  deriving Repr, DecidableEq, BEq

def check (w : Wire) (ask : Offer) : Decision :=
  if w.world ≠ ask.world then .wrongWorld
  else if !w.producers.any (·.matches ask) then .missingProducer
  else if w.child ≠ ask.child ∨ (ask.parent,ask.child) ∉ w.edges then .detached
  else match w.candidates with
    | [d] =>
      if d.id ≠ ask.childKey then .notUnique
      else if d.requirements ≠ [] ∨ w.childTargets ≠ [] then .nonInert
      else if !w.rootHasNominal then .unobserved
      else match w.inspect with
        | none => .unfinished
        | some p => if p.finished then .ready else .unfinished
    | _ => .notUnique

theorem matching_producer (p : Producer) (ask : Offer) : p.matches ask = true ↔
    p.world = ask.world ∧ p.parent = ask.parent ∧ p.parentKey = ask.parentKey ∧
    ask.child ∈ p.children ∧ ask.output ∈ p.targets := by simp [Producer.matches]

theorem check_ready (w : Wire) (ask : Offer) : check w ask = .ready ↔
    w.world = ask.world ∧ (∃ p ∈ w.producers, p.matches ask = true) ∧
    w.child = ask.child ∧ (ask.parent,ask.child) ∈ w.edges ∧
    (∃ d, w.candidates = [d] ∧ d.id = ask.childKey ∧ d.requirements = [] ∧
      w.childTargets = [] ∧ w.rootHasNominal = true ∧ ∃ view, w.inspect = some view ∧ view.finished = true) := by
  by_cases world : w.world = ask.world
  · have anyIff := List.any_eq_true (p := fun x : Producer => x.matches ask) (l := w.producers)
    cases producer : w.producers.any (fun x => x.matches ask) with
    | false =>
      have none : ¬ ∃ p ∈ w.producers, p.matches ask = true := by
        rw [← anyIff,producer]
        decide
      simp [check,world,producer,none]
    | true =>
      have someProducer := anyIff.mp producer
      by_cases belongs : w.child = ask.child ∧ (ask.parent,ask.child) ∈ w.edges
      · obtain ⟨child,edge⟩ := belongs
        cases choices : w.candidates with
        | nil => simp [check,world,producer,someProducer,child,edge,choices]
        | cons d tail =>
          cases tail with
          | cons other rest => simp [check,world,producer,someProducer,child,edge,choices]
          | nil =>
            by_cases keys : d.id = ask.childKey
            · by_cases empty : d.requirements = [] ∧ w.childTargets = []
              · obtain ⟨req,outs⟩ := empty
                cases known : w.rootHasNominal
                · simp [check,world,producer,someProducer,child,edge,choices,keys,req,outs,known]
                · cases view : w.inspect with
                  | none => simp [check,world,producer,someProducer,child,edge,choices,keys,req,outs,known,view]
                  | some summary =>
                    cases done : summary.finished <;>
                      simp [check,world,producer,someProducer,child,edge,choices,keys,req,outs,known,view,done]
              · have conflict : d.requirements ≠ [] ∨ w.childTargets ≠ [] := by
                  by_cases yes : d.requirements = []
                  · exact .inr (fun no => empty ⟨yes,no⟩)
                  · exact .inl yes
                simp [check,world,producer,someProducer,child,edge,choices,keys,conflict]
                exact fun a b => (empty ⟨a,b⟩).elim
            · simp [check,world,producer,someProducer,child,edge,choices,keys]
      · have bad : w.child ≠ ask.child ∨ (ask.parent,ask.child) ∉ w.edges := by
          by_cases one : w.child = ask.child
          · exact .inr (fun two => belongs ⟨one,two⟩)
          · exact .inl one
        rcases bad with id | edge
        · simp [check,world,producer,someProducer,id]
        · simp [check,world,producer,someProducer,edge]
  · simp [check,world]

end Yulang.GeneralRebaseReceiptWire289
