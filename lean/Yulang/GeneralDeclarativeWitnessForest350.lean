import Yulang.GeneralDeclarativeWitnessRecordReplay350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessForest350
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support)
open GeneralDeclarativeWitnessOneRecord350 (Anchor waiting)
open GeneralDeclarativeWitnessRecordReplay350 (Wire Accepted replayCandidate localStep)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralSourceMetadataBareBundle291 (InputBundle compile forget reassemble preserves_input)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (Holds ModelsExact)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Resolves All₂)

structure Layout where
  before : State
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

/-- Every layoutHere certificate sees the identical current declarative state
and immutable source table. The independent problem owns the naming layout. -/
structure ProblemTree where
  source : InputBundle
  current : State
  manifest : Manifest
  layout : List Nat → Demand → Layout

def anchor (p : ProblemTree) (path : List Nat) (d : Demand) : Anchor :=
  let layoutHere := p.layout path d
  ⟨⟨p.source,p.current,d⟩,layoutHere.before,p.manifest,layoutHere.keep,layoutHere.fallback,layoutHere.targets⟩

def emptyReport (d : Demand) : Report :=
  ⟨.pending,.pending,d.outputs⟩

structure Global (p : ProblemTree) where
  table : SourceBundle
  tableOrigin : compile p.source = some table
  live : Attached p.current p.manifest

abbrev rules {p : ProblemTree} (env : Global p) (sidecar : List Entry) :=
  Rule (support env.live) sidecar (registry env.table) (interpretation env.table.snapshot)
    (waiting env.live (registry env.table) (interpretation env.table.snapshot))

theorem proofOnly {s : State} {m : Manifest} (a b : Attached s m) : a = b := by
  cases a; cases b; rfl

theorem replay_same_table {p : Problem} {report : Report} {s t : SourceBundle}
    (header : GeneralDeclarativeWitnessHeader349.replay p ⟨report.outputs⟩ = some s)
    (initial : compile p.source = some t) : s = t := by
  have orig := (GeneralDeclarativeWitnessHeader349.replay_sound header).1
  have known' : GeneralSourceMetadataRoles291.Valid s.roles := by
    unfold GeneralDeclarativeWitnessHeader349.replay at header
    cases first : GeneralDeclarativeWitnessProblem349.first p with
    | none => simp [first] at header
    | some data =>
      rw [first] at header
      change (if _ then some data else none) = some s at header
      split at header
      · cases Option.some.inj header
        exact (GeneralDeclarativeWitnessProblem349.first_sound first).2.1
      · cases header
  have source := reassemble s known'
  rw [orig,initial] at source
  exact (Option.some.inj source).symm

def extendSidecar {s : State} {p : GeneralDeclarativeOrigins321.Supported s done}
    {r i w d impl kids} (old : Selected p a r i w d impl kids) (added : a ⊆ b) :
    Selected p b r i w d impl kids where
  slice := old.slice
  keep := old.keep
  named := old.named
  spans := old.spans
  reads := old.reads
  input := old.input
  fallback := old.fallback
  targets := old.targets
  ordinary := old.ordinary
  compiler := old.compiler
  receipt := old.receipt
  retained := fun _e h => added (old.retained h)
  elected := old.elected

structure Fixed where
  path : List Nat
  demand : Demand
  equations : List Equation

def Fixed.Meaning (f : Fixed) (s : State) : Prop :=
  f.equations.map Equation.left = f.demand.outputs.map GeneralSourceState.Output.target ∧
  ∀ m : Assignment, Models s m → ∀ e ∈ f.equations,GeneralDeclarativeEntailment320.Holds m e

structure Node {p : ProblemTree} (env : Global p) (d : Demand) where
  decl : Declaration
  kids : List Demand
  sidecar : List Entry
  selection : Selected (support env.live) sidecar (registry env.table) (interpretation env.table.snapshot)
    (waiting env.live (registry env.table) (interpretation env.table.snapshot)) d decl kids
  fixed : List Equation
  fixedMeaning : ∀ atPath, (Fixed.mk atPath d fixed).Meaning p.current
  fit : ∀ m : Assignment, Models p.current m → ModelsExact p.current sidecar m

def replayNode {p : ProblemTree} (env : Global p) (path : List Nat) (d : Demand) (wire : Wire) :
    Option (Node env d) := do
  let a ← replayCandidate (anchor p path d) (emptyReport d) wire
  let h : a.table = env.table := replay_same_table a.header env.tableOrigin
  let live : a.live = env.live := proofOnly a.live env.live
  pure ⟨a.decl,a.compiled.compiled.kids,
    GeneralDeclarativeWitnessAllocation350.entries a.projection (anchor p path d).keep,
    h ▸ live ▸ localStep a,wire.emitted.outputRows,
    (fun _ => ⟨by rw [a.compiled.fixed]; exact GeneralDeclarativeWitnessCompiler350.fixed_targets a.compiled.run,
      fun m fit => (GeneralDeclarativeWitnessCompiler350.fixed_in_current a.compiled m fit).2⟩),
    (GeneralDeclarativeWitnessAllocation350.sound a.allocator).2.2⟩

structure Replayed {p : ProblemTree} (env : Global p) (d : Demand) where
  tree : Tree
  sidecar : List Entry
  proof : ∀ b, sidecar ⊆ b → Resolves (rules env b) d tree
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

structure ReplayedList {p : ProblemTree} (env : Global p) (ds : List Demand) where
  trees : List Tree
  sidecar : List Entry
  proof : ∀ b, sidecar ⊆ b → All₂ (Resolves (rules env b)) ds trees
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

mutual
inductive Code where
  | node (layoutHere : Wire) (children : Codes)
inductive Codes where
  | nil
  | cons (first : Code) (remaining : Codes)
end

mutual
/-- The authoritative child inputs are exactly those emitted by the
compiler in sequence. The witness tree carries no replacement demands. -/
def replayTree {p : ProblemTree} (env : Global p) (path : List Nat) (d : Demand) :
    Code → Option (Replayed env d)
  | .node layoutHere child => do
    let head ← replayNode env path d layoutHere
    let tail ← replayList env path 0 head.kids child
    pure ⟨.selected head.decl.id tail.trees,head.sidecar ++ tail.sidecar,
      (fun b covers => .selected (.whole (extendSidecar head.selection
        (fun _ h => covers (List.mem_append_left _ h))))
        (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
      ⟨path,d,head.fixed⟩ :: tail.fixed,
      (fun f h => (List.mem_cons.mp h).elim (fun same => same.symm ▸ head.fixedMeaning path) (tail.fixedMeaning f)),
      (fun m fit e included => (List.mem_append.mp included).elim
        (fun h => (head.fit m fit).2 e h) (fun h => tail.exactIn m fit e h))⟩
termination_by w => sizeOf w

def replayList {p : ProblemTree} (env : Global p) (path : List Nat) (ordinal : Nat) (ds : List Demand) :
    Codes → Option (ReplayedList env ds)
  | .nil =>
    match ds with
    | [] => some ⟨[],[],fun _ _ => .nil,[],fun _ h => False.elim (List.not_mem_nil h),fun _ _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
    | _ :: _ => none
  | .cons first more =>
    match ds with
    | [] => none
    | d :: ds => do
      let head ← replayTree env (path ++ [ordinal]) d first
      let tail ← replayList env path (ordinal+1) ds more
      pure ⟨head.tree :: tail.trees,head.sidecar ++ tail.sidecar,
        (fun b covers => .cons (head.proof b (fun _ h => covers (List.mem_append_left _ h)))
          (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
        head.fixed ++ tail.fixed,
        (fun f h => (List.mem_append.mp h).elim (head.fixedMeaning f) (tail.fixedMeaning f)),
        (fun m fit e included => (List.mem_append.mp included).elim
          (head.exactIn m fit e) (tail.exactIn m fit e))⟩
termination_by w => sizeOf w
end

theorem resolves {p : ProblemTree} {env : Global p} {d : Demand} (r : Replayed env d) :
    Resolves (rules env r.sidecar) d r.tree := r.proof _ (fun _ h => h)

theorem models {p : ProblemTree} {env : Global p} {d : Demand} (r : Replayed env d)
    (m : Assignment) (fit : Models p.current m) : ModelsExact p.current r.sidecar m :=
  ⟨fit,r.exactIn m fit⟩

end Yulang.GeneralDeclarativeWitnessForest350
