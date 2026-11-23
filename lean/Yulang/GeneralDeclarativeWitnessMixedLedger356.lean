import Yulang.GeneralDeclarativeWitnessRecursiveSound356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedLedger356
open GeneralDeclarativeWitnessRecursiveMixed356 (Tree Branches Plan Codes decodeTree)
open GeneralDeclarativeWitnessRecursiveTree356 (view dictionary rows exact_tree)
open GeneralDeclarativeWitnessRecursiveSound356 (Evident one_model_for_whole_tree)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeWitnessMixedScope356 (Scope)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeWitnessCompiler350 (DemandCode printDemand)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeWitnessTypedJoint354 (compatible)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)

structure Entry where
  path : List Nat
  version : Option Nat
  request : DemandCode
  writes : List Write
  deriving DecidableEq

def rootEntry {s : State} (p : Node s) : Entry :=
  ⟨p.origin.path,some p.origin.version,printDemand p.input.demand,p.out.trace⟩

def ordinaryEntry (f : Fixed) : Entry :=
  ⟨f.path,none,printDemand f.demand,f.equations.map Write.ordinary⟩

mutual
def entries {s : State} {e p} (t : @Tree s e p) : List Entry :=
  match t with
  | .typed _ xs => rootEntry p :: entriesBranches xs
termination_by sizeOf t

def entriesBranches {s : State} {e p i ds} (t : @Branches s e p i ds) : List Entry :=
  match t with
  | .nil => []
  | .typed _ got rest => entries got ++ entriesBranches rest
  | .payload _ replay rest => replay.actual.diagnostic.fixed.map ordinaryEntry ++ entriesBranches rest
termination_by sizeOf t
end

def Meaning (m : Assignment) (e : Entry) : Prop :=
  e.writes.map Write.target = e.request.2.2.map Prod.snd ∧ ∀ q ∈ ordinary e.writes,Holds m q

theorem simple_values (xs : List Equation) :
    ordinary (xs.map Write.ordinary) = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih =>
    change h :: ordinary (t.map Write.ordinary) = h :: t
    rw [ih]

theorem only_targets (xs : List Equation) :
    (xs.map Write.ordinary).map Write.target = xs.map Equation.left := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [Write.target,ih]

theorem print_targets (xs : List GeneralSourceState.Output) :
    (xs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd =
      xs.map GeneralSourceState.Output.target := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [GeneralDeclarativeWitnessCompiler350.pair,ih]

theorem mixed_entries_have_exact_targets_and_writes {s : State} {e p} (t : @Tree s e p) (m : Assignment)
    (fit : Models s m) : ∀ a ∈ entries t,Meaning m a := by
  refine @Tree.rec s e
    (fun _ t => ∀ a ∈ entries t,Meaning m a)
    (fun _ _ _ c => ∀ a ∈ entriesBranches c,Meaning m a)
    ?_ ?_ ?_ ?_ p t
  · intro node selected children next a h
    rw [entries.eq_def] at h
    rcases List.mem_cons.mp h with rfl|fromBranch
    · have localWrites := GeneralDeclarativeWitnessTypedRangeWriter354.writes_and_children node.proof m fit
      refine ⟨?_,localWrites.2.2.2⟩
      change node.out.trace.map Write.target =
        (node.input.demand.outputs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd
      rw [print_targets]
      exact localWrites.1
    · exact next a fromBranch
  · intro i node a h
    rw [entriesBranches.eq_def] at h
    cases h
  · intro i d ds node roles wire step below more reduced later a used
    rw [entriesBranches.eq_def] at used
    rcases List.mem_append.mp used with inside|after
    · exact reduced a inside
    · exact later a after
  · intro i d ds node answer route old rest ih a used
    rw [entriesBranches.eq_def] at used
    rcases List.mem_append.mp used with first|tail
    · obtain ⟨f,there,rfl⟩ := List.mem_map.mp first
      obtain ⟨targets,truth⟩ := old.actual.diagnostic.fixedMeaning f there
      refine ⟨?_,?_⟩
      · change (f.equations.map Write.ordinary).map Write.target =
          (f.demand.outputs.map GeneralDeclarativeWitnessCompiler350.pair).map Prod.snd
        rw [only_targets,print_targets]
        exact targets
      · change ∀ q ∈ ordinary (f.equations.map Write.ordinary),Holds m q
        rw [simple_values]
        exact truth m fit
    · exact ih a tail

structure Packet where
  answer : Report
  outputs : List Entry

structure Accepted {s : State} (p : Node s) (e : Scope) (packet : Packet) where
  proof : Tree e p
  compatible : compatible (rows proof) = true
  returned : agrees ⟨p.input.metadata.sourceInput,s,p.input.demand⟩ (view proof) packet.answer = true
  exactOutputs : packet.outputs = entries proof

def read {s : State} (p : Node s) (e : Scope) (ps : List Plan) (code : Codes) (answer : Packet) :
    Option (Accepted p e answer) := do
  let ok ← decodeTree e p ps code
  if b : compatible (rows ok) = true then
    if output : agrees ⟨p.input.metadata.sourceInput,s,p.input.demand⟩ (view ok) answer.answer = true then
      if sorted : answer.outputs = entries ok then
        pure ⟨ok,b,output,sorted⟩
      else none
    else none
  else none

theorem returned_sound {s : State} {p : Node s} {e packet} (a : Accepted p e packet)
    (m : Assignment) (fit : Models s m) :
    packet.answer.tree = view a.proof ∧ packet.answer.result = .selected (dictionary a.proof) ∧
    packet.answer.outputs = p.input.demand.outputs ∧
    (∀ entry ∈ packet.outputs,Meaning m entry) ∧
    ∃ v : Valuation,Evident s m v p.input.demand (dictionary a.proof) := by
  have checked := exact_report a.returned
  exact ⟨checked.1,checked.2.1.trans (exact_tree a.proof),checked.2.2,
    a.exactOutputs.symm ▸ mixed_entries_have_exact_targets_and_writes a.proof m fit,
    one_model_for_whole_tree a.proof a.compatible m fit⟩

end Yulang.GeneralDeclarativeWitnessMixedLedger356
