import Yulang.GeneralDeclarativeWitnessActualOpenBody359
import Yulang.GeneralDeclarativeWitnessRecursiveSeed358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralDeclarativeWitnessActualOpenReceipts359
open GeneralDeclarativeWitnessCompiler350
  (Context Finished Wire Accepted execute decode exact_children fixed_in_current printDemand)
open GeneralDeclarativeWitnessRecursiveSeed358 (plan)
open GeneralDeclarativeOpenFixtureBase339 (registry decl root keep fallback targets)
open GeneralDeclarativeOpenFixtureRoutes339 (w2 used)
open GeneralDeclarativeOpenFixtureSelection339
  (rootFinal final child childUses childWrite rootWrite root_compiles child_compiles)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)

def atRoot : Context := ⟨registry,interpretation,root,decl,w2.state,used,keep,fallback,targets⟩
def atChild (d : Demand) : Context := ⟨registry,interpretation,d,leaf,rootFinal,childUses,keep,fallback,targets⟩

structure Receipt where
  root : Wire
  child : Wire

def prepare : Option Receipt := do
  let parent ← execute atRoot
  let [actual] := parent.kids | none
  let sub ← execute (atChild actual)
  pure ⟨plan parent final,plan sub final⟩

structure Checked (r : Receipt) where
  parent : Accepted atRoot final r.root
  reached : Demand
  actual : parent.compiled.kids = [reached]
  sub : Accepted (atChild reached) final r.child
  endHere : sub.compiled.kids = []

def replay (r : Receipt) : Option (Checked r) := do
  let root ← decode atRoot final r.root
  match child : root.compiled.kids with
  | [d] => do
    let sub ← decode (atChild d) final r.child
    if stop : sub.compiled.kids = [] then
      some ⟨root,d,child,sub,stop⟩
    else none
  | _ => none

def observe (r : Receipt) : Bool :=
  (replay r).isSome &&
  decide (r.root.children = [printDemand child] ∧ r.child.children = []) &&
  decide (r.root.outputRows = [rootWrite] ∧ r.child.outputRows = [childWrite])

theorem literal_becomes_checked : (prepare.map observe).getD false = true := by decide +kernel

theorem parent_emits_actual_nonpoint {r : Receipt} (a : Checked r) :
    a.reached = child ∧ a.reached.arguments = [⟨19,14,20⟩] := by
  have actual := GeneralDeclarativeWitnessCompiler350.actual a.parent
  have known := root_compiles
  change _ = some (rootFinal,[child]) at known
  have eq := congrArg Prod.snd (Option.some.inj (actual.symm.trans known))
  have childEqual : a.reached = child := List.cons.inj (a.actual.symm.trans eq) |>.1
  refine ⟨childEqual,?_⟩
  rw [childEqual]

theorem both_literal_outputs {r : Receipt} (checked : Checked r) (m : Assignment) (fit : Models final m) :
    r.root.outputRows.map Equation.left = [6] ∧ r.child.outputRows.map Equation.left = [5] ∧
    (∀ eq ∈ r.root.outputRows,Holds m eq) ∧ ∀ eq ∈ r.child.outputRows,Holds m eq := by
  have p := fixed_in_current checked.parent m fit
  have c := fixed_in_current checked.sub m fit
  have same := (parent_emits_actual_nonpoint checked).1
  exact ⟨p.1,(by simpa [atChild,same] using c.1),p.2,c.2⟩

def changedCenter : Demand := ⟨2,[⟨19,11,20⟩],[⟨1,5⟩]⟩
def swapsRootSource (r : Receipt) : Receipt :=
  {r with root := {r.root with outputRows := [⟨6,.variable 17⟩]}}
def changesChildCenter (r : Receipt) : Receipt :=
  {r with root := {r.root with children := [printDemand changedCenter]}}
def swapsWrites (r : Receipt) : Receipt :=
  ⟨{r.root with outputRows := r.child.outputRows},{r.child with outputRows := r.root.outputRows}⟩

theorem actual_compiler_rejects_relabeling :
    (prepare.map fun r => (replay (swapsRootSource r)).isSome ||
      (replay (changesChildCenter r)).isSome || (replay (swapsWrites r)).isSome).getD true = false := by
  decide +kernel

/-- In the very same real compiler fixture both tails are literally the
same closed producer value, but the actual lexical receipt cannot swap
the root's residual name for the child's nested residual name. -/
theorem model_equality_does_not_rewrite_receipt :
    ∃ r : Receipt, prepare = some r ∧ (replay r).isSome = true ∧
      (replay (swapsRootSource r)).isSome = false ∧
      ∃ m, GeneralDeclarativeExactOverlay337.ModelsExact final w2.reads m ∧ (m 11).1 = (m 17).1 := by
  have ok := literal_becomes_checked
  have negative := actual_compiler_rejects_relabeling
  cases raw : prepare with
  | none => rw [raw] at ok; cases ok
  | some r =>
    rw [raw] at ok negative
    have accepted : observe r = true := ok
    have first := (GeneralDeclarativeWitnessProblem349.splitAnd
      (GeneralDeclarativeWitnessProblem349.splitAnd accepted).1).1
    have nope : ((replay (swapsRootSource r)).isSome ||
      (replay (changesChildCenter r)).isSome || (replay (swapsWrites r)).isSome) = false := negative
    have missing : (replay (swapsRootSource r)).isSome = false :=
      (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp nope).1).1
    obtain ⟨m,fits,tail11,tail17⟩ := GeneralDeclarativeOpenFixtureModel339.inhabited
    exact ⟨r,rfl,first,missing,m,fits,tail11.trans tail17.symm⟩

end Yulang.GeneralDeclarativeWitnessActualOpenReceipts359
