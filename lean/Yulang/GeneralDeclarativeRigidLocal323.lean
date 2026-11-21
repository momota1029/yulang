import Yulang.GeneralDeclarativeRigidBatch323
import Yulang.GeneralDeclarativeOutputRequests323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidLocal323
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeRigidSource323 (Ordered compiled_results)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeSemanticSharing323 (SharedAt SameBinder FirstNames exact_shared)
open GeneralDeclarativeEntailment320 (Entails appendFacts BatchRecipe)
open GeneralDeclarativeOutputSplit323 (lift_entails)
open GeneralDeclarativeOutputSource323 (Declared generated declared_rows)
open GeneralDeclarativeRootClosure323 (DeclaredRows exact_rows)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeNodeFacts320 (nodeFacts clauseFacts)
open GeneralDeclarativeEmissionForest322 (Placement children all_clauses)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeBatch320 (collect)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)

structure RigidReads (s : State) (r : Registry) (interp : Interpretation) (d : Demand)
    (impl : Declaration) (names : Names) (place : Placement) : Prop where
  seen : ∃ occ, Ordered s r.constructors interp d.arguments impl.head occ ∧
    FirstNames s occ names.input ∧ SameBinder s occ
  boundCaptured : ∀ x ∈ impl.inputNames, Bounds s (names.input x)
  boundArguments : ∀ arg ∈ d.arguments, Bounds s arg
  coherent : Agree impl names
  clauseReads : ∀ clause ∈ impl.requirements,
    Ready s r interp impl clause names (place.compound clause) (place.targets clause)

/-- Fixed roots use ordinary associated equalities from the state, for
the actual normalized source capture and actual source request. No
condition on solver execution or recursive dictionaries appears here. -/
def RootClosed (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (impl : Declaration) (capture : Nat → Capture) : Prop :=
  ∀ out ∈ d.outputs, ∀ row, rootFact r interp impl d capture out = some [row] → Entails s row


theorem exact_batch {s : State} (checked : Checked r) (cover : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role)
    (asks : Declared r d) (reads : RigidReads s r interp d impl names place)
    (closed : RootClosed s r interp d impl names.input) :
    BatchRecipe s r interp d impl.id (children impl names place) := by
  obtain ⟨occ,views,first,shared⟩ := reads.seen
  obtain ⟨a,ha,ea⟩ := compiled_results views ((exact_shared views first).mpr shared)
  obtain ⟨b,hb,eb⟩ := all_clauses reads.coherent reads.clauseReads
  obtain ⟨c,hc⟩ := generated (capture := names.input) checked cover visible role asks
  refine ⟨impl,names.input,a++b++c,rfl,visible,reads.boundCaptured,reads.boundArguments,
    by simp [nodeFacts,role,ha,hb,hc],?_⟩
  intro row listed
  rcases List.mem_append.mp listed with before|output
  · exact (List.mem_append.mp before).elim (ea row) (eb row)
  · obtain ⟨out,wanted,wrote⟩ := (exact_rows (declared_rows checked cover visible role asks) hc).mp output
    exact closed out wanted row wrote

end Yulang.GeneralDeclarativeRigidLocal323
