import Yulang.GeneralRebaseReceiptScopedTrace289

/-! Compile one output-mark template: if the parent head is F(a) and its
associated body is F(F(a)), a point parent input can be used as the
argument of the outer F in the mark. This is an auxiliary finite code,
not a generic expression compiler or an old Knowledge operation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseReceiptCompile289
open GeneralDeclarations (Declaration)
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseRowChildSource287
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptFixture289 (request)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent nominal)

structure Mark where
  target : Nat
  constructor : Nat
  argument : Nat
  deriving Repr, DecidableEq, BEq

def Mark.Holds (code : Mark) (m : Assignment) : Prop :=
  Equivalent (m code.target).1 (nominal code.constructor [.inl (m code.argument).1])

def compile (r : Occurrence rs) (ask : Offer) : Option Mark :=
  if r.identity ≠ ask.parent then none else
  match ask.world.find? (fun d => d.id == ask.parentKey), List.ofFn r.demand.arguments, r.demand.outputs with
  | some d, [bounds], [wanted] =>
    match d.head, d.associated with
    | [.app ctor [.var binder]], [out] =>
      match out.rhs with
      | .app outer [.app nested [.var used]] =>
        if outer = ctor ∧ nested = ctor ∧ used = binder ∧
            bounds.1 = bounds.2 ∧ wanted.name = out.name ∧ wanted.target = ask.output
        then some ⟨wanted.target,ctor,bounds.1⟩ else none
      | _ => none
    | _,_ => none
  | _,_,_ => none

def observe (r : Occurrence rs) : GeneralRebaseReceiptMachine289.Phase → Option Mark
  | .published stamp => compile r stamp
  | _ => none

abbrev actualMark : Mark := ⟨2,0,1⟩

theorem concrete_compile (choice : Bool) : compile root (request choice) = some actualMark := by
  cases choice <;> decide +kernel

theorem compile_has_offered_target (r : Occurrence rs) (ask : Offer) (value : Mark)
    (found : compile r ask = some value) : value.target = ask.output := by
  unfold compile at found
  split at found
  · contradiction
  · split at found
    · rename_i declaration bounds wanted _
      split at found
      · split at found
        · split at found
          · rename_i ok
            cases Option.some.inj found
            exact ok.2.2.2.2.2
          · contradiction
        · contradiction
      · contradiction
    · contradiction

end Yulang.GeneralRebaseReceiptCompile289
