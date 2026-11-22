import Yulang.GeneralDeclarativeWitnessCovariantCompiler353
import Yulang.GeneralDeclarativeWitnessCovariantWrittenState353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedOutput354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeWitnessCovariantCompiler353 (Prepared)
open GeneralDeclarativeWitnessCovariantMetadata353 (Checked check)
open GeneralDeclarativeWitnessCompiler350 (Context)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open GeneralSourceState (Output)
open GeneralDictionaryAssociatedProvenance (lookup Supplies lookup_exact)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeNormalizeAssoc324 (one)

structure Typed (p : Problem) (c : Context) (input : Nat → Capture) (out : Output) where
  authored : GeneralDeclarations.Equation
  found : lookup c.registry.roles c.decl out.name = some (.explicit authored)
  tag : Nat
  box : Nat
  binder : Nat
  written : authored.rhs = .variant tag (.app box [.var binder])
  declared : Checked p.metadata box
  actualBinder : binder ∈ c.decl.inputNames

def Typed.row {p c input out} (a : Typed p c input out) : Row :=
  ⟨out.target,a.tag,a.box,(input a.binder).center⟩

def typed (p : Problem) (c : Context) (input : Nat → Capture) (out : Output) : Option (Typed p c input out) :=
  match found : lookup c.registry.roles c.decl out.name with
  | some (.explicit eqn) =>
    match written : eqn.rhs with
    | .variant tag (.app box [.var binder]) =>
      if used : binder ∈ c.decl.inputNames then do
        let decl ← check p.metadata box
        pure ⟨eqn,found,tag,box,binder,written,decl,used⟩
      else none
    | _ => none
  | _ => none

theorem supplies {p c input out} (a : Typed p c input out)
    (unique : (c.decl.associated.map GeneralDeclarations.Equation.name).Nodup) :
    Supplies c.registry.roles c.decl out.name (.explicit a.authored) :=
  (lookup_exact _ _ unique _ _).mp a.found

inductive Write where
  | ordinary (eqn : Equation)
  | typed (row : Row)
  deriving DecidableEq

def Write.target : Write → Nat
  | .ordinary e => e.left
  | .typed e => e.root

inductive Item (p : Problem) (c : Context) (input : Nat → Capture) (out : Output) where
  | nominal (a : Typed p c input out)
  | ordinary (e : Equation) (run : one c.registry c.interp c.decl c.demand input out = some [e])
      (target : e.left = out.target)

def Item.write {p c input out} : Item p c input out → Write
  | .nominal a => .typed a.row
  | .ordinary e _ _ => .ordinary e

theorem item_target {p c input out} (a : Item p c input out) : a.write.target = out.target := by
  cases a with
  | nominal _ => rfl
  | ordinary _ _ h => exact h

def item (p : Problem) (c : Context) (input : Nat → Capture) (out : Output) : Option (Item p c input out) :=
  match typed p c input out with
  | some a => some (.nominal a)
  | none =>
    match compiled : one c.registry c.interp c.decl c.demand input out with
    | some [e] => if target : e.left = out.target then some (.ordinary e compiled target) else none
    | _ => none

inductive Batch (p : Problem) (c : Context) (input : Nat → Capture) : List Output → Type where
  | nil : Batch p c input []
  | cons : Item p c input o → Batch p c input os → Batch p c input (o::os)

def Batch.trace {p c input outs} : Batch p c input outs → List Write
  | .nil => []
  | .cons a bs => a.write :: bs.trace

def batch (p : Problem) (c : Context) (input : Nat → Capture) : (outs : List Output) → Option (Batch p c input outs)
  | [] => some .nil
  | o::os => do
    let a ← item p c input o
    let b ← batch p c input os
    pure (.cons a b)

theorem trace_targets {p c input outs} (b : Batch p c input outs) :
    b.trace.map Write.target = outs.map Output.target := by
  induction b with
  | nil => rfl
  | cons x _ ih => simp only [Batch.trace,List.map_cons,item_target,ih]

def ordinary (xs : List Write) : List Equation :=
  xs.filterMap fun | .ordinary e => some e | .typed _ => none

def typedRows (xs : List Write) : List Row :=
  xs.filterMap fun | .typed r => some r | .ordinary _ => none

end Yulang.GeneralDeclarativeWitnessTypedOutput354
