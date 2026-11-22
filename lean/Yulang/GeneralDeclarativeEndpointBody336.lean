import Yulang.GeneralDeclarativeNestedBody332
import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointBody336
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeStableTies329 (Consequence pairOf)
open GeneralDeclarativeStableAssemble329 (merged tieState assemble prepare_grows)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativeOpaqueShared328 (Chosen)
open GeneralDeclarativeOpaqueBatch328 (check_exact)
open GeneralDeclarativeEntailment320 (appendFacts conservative_append)
open GeneralDeclarativeGrowth327 (Extends facts trans fits restrict)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeAppliedClause327 (prepared_exists targetsOnly compiled_frames)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeFrameReadback325 (sourceNames clause)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeProducedNames325 (exact_input coherent)
open GeneralDeclarativeInPlace327 (clause_here)
open GeneralDeclarativeNFEmit324 (ordinary_forest)
open GeneralDeclarativeNFWhere324 (clauses_sound)
open GeneralDeclarativeNFNode324 (output_meaning)
open GeneralDeclarativeAppliedSource325 (stable_after_written)
open GeneralDeclarativeAssembly320 (ChildDenotes)
open GeneralDeclarativeOutputs320 (OutputMeaning)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

/-- The actual ordinary compiler's body frame. Unlike the old whole
frame, this record does not demand equality of the actual input and a
literal record expression. It is reconstructed from compileBody and
the names/intervals of actual, independently certified captures. -/
structure Body {r : Registry} {i : Interpretation} {d : Demand} {impl : Declaration}
    (s : State) (kids : List Demand) where
  base : Nat → Capture
  spans : List (Nat × Capture)
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
  ordered : children impl (sourceNames impl (placement impl.requirements ports targets) base)
    (placement impl.requirements ports targets) = kids

def Body.capture {r i d impl s kids} (b : @Body r i d impl s kids) : Nat → Capture :=
  (sourceNames impl (placement impl.requirements b.ports b.targets) b.base).input

def from_frame (b : Frame s r i d impl kids) : @Body r i d impl s kids :=
  ⟨b.base,b.spans,b.tied,b.ranges,b.targets,b.keep,b.inputState,b.prepared,b.ports,b.inputRead,
    b.current,b.whereRows,b.whereWritten,b.whereHere,b.rootRows,b.rootWritten,b.rootHere,check_exact.mp b.ordered⟩

/-- Same body calculation as C332. The only source use of the old
head walk in this construction was its exact binder occurrence order. -/
theorem calculate {s : State} {d : Demand} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (demand : Declared r d)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat)
    (binderOrder : spans.map Prod.fst = impl.inputNames)
    (fit : ∀ a ∈ spans, Bounds s a.2) :
    ∃ (current : State) (kids : List Demand) (body : @Body r i d impl current kids),
      let input := merged s keep spans fallback
      compileBody r i d impl s spans keep fallback targets = some (current,kids) ∧
      body.base = input.captures ∧ body.spans = spans ∧ body.targets = targets ∧
      current = appendFacts (appendFacts body.prepared body.whereRows) body.rootRows ∧
      Extends (tieState s spans fallback) current := by
  let input := merged s keep spans fallback
  have built := assemble keep spans fallback fit
  obtain ⟨prep,ports,ready⟩ := prepared_exists (s := input.state) covered visible targets input.captures keep
  let place := placement impl.requirements ports targets
  let named := sourceNames impl place input.captures
  obtain ⟨ws,rs,atWhere,atRoot,_,_,_,_,_⟩ :=
    compiled_frames checked covered visible role demand targets input.captures keep ready
  let current := appendFacts (appendFacts prep ws) rs
  let kids := children impl named place
  have appended : Extends prep current := trans (facts _ _) (facts _ _)
  have grown : Extends input.state current := trans (prepare_grows ready) appended
  have has : ∀ v ∈ impl.inputNames, Bounds current (input.captures v) := by
    intro v listed
    rw [← binderOrder] at listed
    obtain ⟨span,found,rfl⟩ := List.mem_map.mp listed
    exact fits grown (built.ranges span found)
  have ties : Consequence current input.captures (spans.map pairOf) :=
    fun e member m fit => built.written e member m (restrict grown m fit)
  let body : @Body r i d impl current kids :=
    ⟨input.captures,spans,ties,has,targets,stateNames input.state ++ keep,input.state,prep,ports,
      ready,appended,ws,atWhere,fun _ h => List.mem_append_left _ (List.mem_append_right _ h),
      rs,atRoot,fun _ h => List.mem_append_right _ h,rfl⟩
  refine ⟨current,kids,body,?_,rfl,rfl,rfl,rfl,trans built.preserve.grows grown⟩
  unfold compileBody
  change (do
    let (prepared,ports) ← prepare r.constructors i (stateNames input.state ++ keep)
      (sourceNames impl (targetsOnly targets) input.captures).input input.state impl.requirements
    let place := placement impl.requirements ports targets
    let chosen := sourceNames impl place input.captures
    let whereRows ← whole r i impl chosen targets
    let rootRows ← collect (one r i impl d chosen.input) d.outputs
    pure (appendFacts (appendFacts prepared whereRows) rootRows,children impl chosen place)) = some (current,kids)
  simp [ready,atWhere,atRoot,place,named,current,kids]

structure Meaning (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand)
    (impl : Declaration) (cap : Nat → Capture) (kids : List Demand) : Prop where
  visible : impl ∈ r.declarations
  role : impl.role = d.role
  captures : ∀ name ∈ impl.inputNames,
    InInterval (m (cap name).lower).1 (m (cap name).upper).1 (m (cap name).center).1
  children : All₂ (ChildDenotes r.constructors i cap m) impl.requirements kids
  outputs : ∀ out ∈ d.outputs, OutputMeaning r.roles r.constructors i impl d cap m out

theorem sound {r i d impl s kids} (b : @Body r i d impl s kids)
    (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (m : Assignment) (valid : Models s m) :
    Meaning r i m d impl b.capture kids ∧ ∀ child ∈ kids, Declared r child := by
  let place := placement impl.requirements b.ports b.targets
  let names := sourceNames impl place b.base
  have well := checked.2 impl visible
  have bounded : ∀ n ∈ impl.inputNames, Bounds s (names.input n) := by
    intro n used
    unfold names sourceNames
    rw [exact_input well used]
    exact b.ranges n used
  obtain ⟨rows,wrote,truth⟩ := ordinary_forest (coherent _ _ _)
    (fun cl known => clause (clause_here checked coverage visible b.inputRead b.current
      b.whereWritten b.whereHere known))
  obtain ⟨cover,stable⟩ := stable_after_written checked visible b.rootWritten b.rootHere
  refine ⟨⟨visible,role,fun n h => bounds_sound (bounded n h) m valid,?_,
    output_meaning checked visible role wanted cover stable m valid⟩,?_⟩
  · change All₂ (ChildDenotes r.constructors i names.input m) impl.requirements kids
    rw [← b.ordered]
    exact clauses_sound (s := appendFacts s rows) well bounded wrote (fun _ h => List.mem_append_right _ h)
      m ((conservative_append truth m).mpr valid)
  · intro child included
    exact child_declared checked visible (b.ordered.symm ▸ included)

end Yulang.GeneralDeclarativeEndpointBody336
