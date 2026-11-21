import Yulang.GeneralDeclarativeStableReads329
import Yulang.GeneralDeclarativeOpaqueBatch328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableCompiler329
open GeneralDeclarations (Checked Declaration Registry Clause)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeStableReads329 (Heads head)
open GeneralDeclarativeStableTies329 (Consequence pairOf)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)

theorem source_ties {s : State} {d : Demand} (checked : Checked r) (visible : impl ∈ r.declarations)
    (observed : Heads s r.constructors i d.arguments impl.head spans)
    (tied : Consequence s base (spans.map pairOf)) (place : GeneralDeclarativeEmissionForest322.Placement) :
    Consequence s (sourceNames impl place base).input (spans.map pairOf) := by
  intro fact written
  obtain ⟨u,found,rfl⟩ := List.mem_map.mp written
  obtain ⟨use,different⟩ := List.mem_filter.mp found
  obtain ⟨span,known,rfl⟩ := List.mem_map.mp use
  have inNames : span.1 ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,← GeneralDeclarativeStableReads329.names_all observed]
    exact List.mem_map.mpr ⟨_,known,rfl⟩
  have same : (sourceNames impl place base).input span.1 = base span.1 :=
    GeneralDeclarativeProducedNames325.exact_input (checked.2 impl visible) inNames
  rw [GeneralDeclarativeStableTies329.row,pairOf,same]
  change GeneralDeclarativeEntailment320.Entails s (GeneralDeclarativeStableTies329.row base (pairOf span))
  exact tied _ (List.mem_map.mpr ⟨pairOf span,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,known,rfl⟩,
    by simpa only [pairOf,same] using different⟩,rfl⟩)

/-- Everything consumed by the ordinary compiler is in the supplied
current state. Endpoints authorize candidate probing separately.
The head walk lists real centers, the selected equation batch relates
them, and the prepare result provides the actual ordered child list. -/
structure Frame (s : State) (r : Registry) (i : Interpretation) (d : Demand)
    (impl : Declaration) (kids : List Demand) where
  base : Nat → Capture
  spans : List (Nat × Capture)
  observed : Heads s r.constructors i d.arguments impl.head spans
  tied : Consequence s base (spans.map pairOf)
  ranges : ∀ a ∈ impl.inputNames, Bounds s (base a)
  targets : Clause → Nat → Nat
  keep : List Nat
  inputState : State
  prepared : State
  ports : List Port
  inputRead : prepare r.constructors i keep (sourceNames impl (targetsOnly targets) base).input
    inputState impl.requirements = some (prepared,ports)
  current : Extends prepared s
  whereRows : List Equation
  whereWritten : whole r i impl (sourceNames impl (placement impl.requirements ports targets) base)
    targets = some whereRows
  whereHere : whereRows ⊆ s.equations
  rootRows : List Equation
  rootWritten : collect (one r i impl d (sourceNames impl (placement impl.requirements ports targets) base).input)
    d.outputs = some rootRows
  rootHere : rootRows ⊆ s.equations
  ordered : check (children impl (sourceNames impl (placement impl.requirements ports targets) base)
    (placement impl.requirements ports targets)) kids = true

def Frame.capture (b : Frame s r i d impl kids) : Nat → Capture :=
  (sourceNames impl (placement impl.requirements b.ports b.targets) b.base).input

theorem read {s : State} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (frame : Frame s r i d impl kids) :
    Result s (facts r i frame.capture impl d kids) ∧
    (∀ m, Models s m → Meaning r i m d impl frame.capture kids) ∧
    ∀ child ∈ kids, Declared r child := by
  have same := (check_exact.mp frame.ordered).symm
  let place := placement impl.requirements frame.ports frame.targets
  have headSeen := head frame.observed (source_ties checked visible frame.observed frame.tied place)
  obtain ⟨compiled,localSound⟩ := GeneralDeclarativeInPlace327.current_sound checked covered visible role wanted
    frame.inputRead frame.current frame.whereWritten frame.whereHere frame.rootWritten frame.rootHere frame.ranges headSeen
  refine ⟨?_,?_,?_⟩
  · simpa only [Frame.capture,same] using compiled
  · intro m fits
    simpa only [Frame.capture,same] using localSound m fits
  · intro child here
    exact GeneralDeclarativeOutputRequests323.child_declared checked visible (same ▸ here)

end Yulang.GeneralDeclarativeStableCompiler329
