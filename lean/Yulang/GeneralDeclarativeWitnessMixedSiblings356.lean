import Yulang.GeneralDeclarativeWitnessMixedTyped356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedSiblings356
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessMixedScope356 (Scope Ordinary ordinary_same_model)
open GeneralDeclarativeWitnessPayloadRoute356 (Route ordinary_payload_law)
open GeneralDeclarativeWitnessMixedTyped356 (Typed)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation HasView Row)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessNominalSpine355 (classified node_is_sound)
open GeneralDeclarativeWitnessTypedEvidence355 (Evidence compose)
open GeneralDeclarativeWitnessTypedJoint354 (compatible shared author_rows)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary Tree Result All₂ classification classifications classification_exact classifications_exact)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)

inductive Plan where
  | typed (a : GeneralDeclarativeWitnessMixedTyped356.Plan)
  | payload (clause binder : Nat)

inductive BranchWire where
  | typed (c : GeneralDeclarativeWitnessMixedTyped356.Wire)
  | payload (path : List Nat) (c : GeneralDeclarativeWitnessMixedForest352.Code) (ordinaryReport : Report)

inductive Child {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand) where
  | typed {a w} : Typed p e idx d a w → Child p e idx d
  | payload {r} : Route p idx d →
      Ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [idx]) d r → Child p e idx d

def child {s : State} (p : Node s) (e : Scope) (idx : Nat) (d : Demand) :
    Plan → BranchWire → Option (Child p e idx d)
  | .typed a,.typed w => (GeneralDeclarativeWitnessMixedTyped356.subtree p e idx d a w).map .typed
  | .payload clause binder,.payload path wire out =>
    if path = p.origin.path ++ [idx] then do
      let projection ← GeneralDeclarativeWitnessPayloadRoute356.read p idx d clause binder
      let passed ← GeneralDeclarativeWitnessMixedScope356.ordinary e p.input.metadata.sourceInput s
        (p.origin.path ++ [idx]) d wire out
      pure (.payload projection passed)
    else none
  | _,_ => none

def Child.tree {s : State} {p : Node s} {e i d} : Child p e i d → Tree
  | .typed a => a.subtree.tree
  | .payload _ a => a.actual.diagnostic.tree

def Child.dictionary {s : State} {p : Node s} {e i d} : Child p e i d → Dictionary
  | .typed a => a.subtree.dictionary
  | .payload _ a => a.dictionary

def Child.rows {s : State} {p : Node s} {e i d} : Child p e i d → List Row
  | .typed a => a.subtree.rows
  | .payload _ _ => []

theorem Child.classified_here {s : State} {p : Node s} {e i d} (a : Child p e i d) :
    classification a.tree = .selected a.dictionary := by
  cases a with
  | typed a => exact classified a.subtree
  | payload _ a => exact (exact_report a.actual.exactResult).2.1.symm.trans a.exactDict

inductive Sons {s : State} (p : Node s) (e : Scope) : Nat → List Demand → Type where
  | nil : Sons p e idx []
  | cons : Child p e idx d → Sons p e (idx+1) ds → Sons p e idx (d::ds)

def children {s : State} (p : Node s) (e : Scope) (idx : Nat) :
    (ds : List Demand) → List Plan → List BranchWire → Option (Sons p e idx ds)
  | [],[],[] => some .nil
  | d::ds,a::as,w::ws => do
    let found ← child p e idx d a w
    let rest ← children p e (idx+1) ds as ws
    pure (.cons found rest)
  | _,_,_ => none

def Sons.trees {s : State} {p : Node s} {e idx ds} : Sons p e idx ds → List Tree
  | .nil => []
  | .cons one rest => one.tree :: rest.trees

def Sons.dictionaries {s : State} {p : Node s} {e idx ds} : Sons p e idx ds → List Dictionary
  | .nil => []
  | .cons one rest => one.dictionary :: rest.dictionaries

def Sons.rows {s : State} {p : Node s} {e idx ds} : Sons p e idx ds → List Row
  | .nil => []
  | .cons one rest => one.rows ++ rest.rows

theorem Sons.all_classify {s : State} {p : Node s} {e idx ds} (a : Sons p e idx ds) :
    classifications a.trees = a.dictionaries.map Result.selected := by
  induction a with
  | nil => rfl
  | cons first rest ih =>
    change classification first.tree :: classifications rest.trees =
      .selected first.dictionary :: rest.dictionaries.map Result.selected
    rw [first.classified_here,ih]

/-- The ordinary branch reads the explicitly emitted merged payload
using its own source chemistry and original ordinary evidence kernel.
It never receives the typed valuation as an ordinary assumption. -/
def MixedEvidence {s : State} (p : Node s) (m : Assignment) (v : Valuation)
    (d : Demand) (dict : Dictionary) : Prop :=
  Evidence s m v d dict ∨
    ∃ (e : Scope) (i : Nat) (out : Report) (_projection : Route p i d) (cert : Ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [i]) d out),
      dict = cert.dictionary ∧
      GeneralDeclarativeExactDictionary337.Evidence
        (registry cert.actual.global.table) (interpretation cert.actual.global.table.snapshot) m d dict ∧
      (∃ cap, d.arguments = [cap] ∧ cap.center = p.valueName ∧
        CommonNominalFullCarrier.Equivalent (m cap.center).1
          (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
                  (m p.proof.compiled.readFrom.center.anchor.last.valueName).1)) ∧
      (∀ f ∈ cert.actual.diagnostic.fixed,f.equations.map Equation.left =
        f.demand.outputs.map GeneralSourceState.Output.target ∧ ∀ q ∈ f.equations,Holds m q)

theorem Child.meaning {s : State} {p : Node s} {e i d} (a : Child p e i d)
    (m : Assignment) (fit : Models s m) (v : Valuation) (all : ∀ row ∈ a.rows,HasView m v row) :
    MixedEvidence p m v d a.dictionary := by
  cases a with
  | typed a =>
    unfold MixedEvidence
    apply Or.inl
    exact compose a.subtree m fit v (fun n h =>
      node_is_sound n m fit v (fun row has => all row (List.mem_flatMap.mpr ⟨n,h,has⟩)))
  | payload projection a =>
    have meaning := ordinary_same_model a m fit
    exact .inr ⟨_,_,_,projection,a,rfl,meaning.1,ordinary_payload_law projection m fit,meaning.2.1⟩

theorem Sons.same_model {s : State} {p : Node s} {e idx ds} (a : Sons p e idx ds)
    (m : Assignment) (fit : Models s m) (v : Valuation) (all : ∀ row ∈ a.rows,HasView m v row) :
    All₂ (MixedEvidence p m v) ds a.dictionaries := by
  induction a with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (head.meaning m fit v (fun row h => all row (List.mem_append_left _ h)))
      (ih (fun row h => all row (List.mem_append_right _ h)))

structure Accepted {s : State} (p : Node s) (e : Scope) (answer : Report) where
  typedRole : p.input.demand.role ∈ e.typedRoles
  children : Sons p e 0 p.proof.compiled.children
  compatible : compatible (p.input.rows ++ children.rows) = true
  report : agrees ⟨p.input.metadata.sourceInput,s,p.input.demand⟩ (.selected p.name children.trees) answer = true

def decode {s : State} (p : Node s) (e : Scope) (ps : List Plan) (codes : List BranchWire)
    (out : Report) : Option (Accepted p e out) := do
  if typed : p.input.demand.role ∈ e.typedRoles then
    let verified ← children p e 0 p.proof.compiled.children ps codes
    if good : compatible (p.input.rows ++ verified.rows) = true then
      if answer : agrees ⟨p.input.metadata.sourceInput,s,p.input.demand⟩ (.selected p.name verified.trees) out =
          true then
        some ⟨typed,verified,good,answer⟩
      else none
    else none
  else none

theorem sound {s : State} {p : Node s} {e out} (a : Accepted p e out) (m : Assignment) (fit : Models s m) :
    out.tree = .selected p.name a.children.trees ∧
    out.result = .selected (.node p.name a.children.dictionaries) ∧
    out.outputs = p.input.demand.outputs ∧
    ∃ v : Valuation,
      GeneralDeclarativeWitnessTypedEvidence355.Local m v p ∧
      All₂ (MixedEvidence p m v) p.proof.compiled.children a.children.dictionaries := by
  have report := exact_report a.report
  have chosen : classification (.selected p.name a.children.trees) =
      .selected (.node p.name a.children.dictionaries) :=
    (classification_exact ..).mpr (.selected ((classifications_exact ..).mp a.children.all_classify) (.selected rfl))
  let actual := shared p.input (p.input.rows ++ a.children.rows) m
  have h : ∀ row ∈ p.input.rows ++ a.children.rows,HasView m actual row := author_rows a.compatible m
  have root := node_is_sound p m fit actual (fun r used => h r (List.mem_append_left _ used))
  exact ⟨report.1,report.2.1.trans chosen,report.2.2,⟨actual,
    GeneralDeclarativeWitnessTypedEvidence355.all_input_binders_in_same_model p m fit actual root,
    a.children.same_model m fit actual (fun r used => h r (List.mem_append_right _ used))⟩⟩

end Yulang.GeneralDeclarativeWitnessMixedSiblings356
