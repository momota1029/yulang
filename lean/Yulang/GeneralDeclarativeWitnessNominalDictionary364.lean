import Yulang.GeneralDeclarativeWitnessActualNominalLeaf364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 88000
set_option maxHeartbeats 120000000
namespace Yulang.GeneralDeclarativeWitnessNominalDictionary364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Query rootQuery)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (exact_endpoint_provenance)
open GeneralDeclarativeWitnessElectedPayload364 (independent_center_read_after_election)
open GeneralDeclarativeWitnessActualNominalLeaf364 (FinishedRun demo actual)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence dictionary_sound)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessNativeValue360 (Value)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Classify)

def childQuery {contra x} (z : @FinishedRun contra x) : Query := ⟨[10,0],z.inspected.sourceRoot.occurrence⟩

inductive Local {contra : Bool} {x : Ordered contra} (z : FinishedRun x) : Query → Frontier Query → Prop where
  | root : Local z rootQuery (.selected z.inspected.sourceRoot.chosen.impl.id [childQuery z])
  | typed : Local z (childQuery z) (.selected z.leaf.elected.row.id [])

structure NominalMeaning {contra : Bool} {x : Ordered contra} (z : FinishedRun x)
    (m : Assignment) (v : NativeViews) : Prop where
  prior : Fits z.inspected.sourceRoot.world m v
  first : v 301 = some (.unary z.leaf.elected.unary.ctor
      (.leaf (m z.inspected.independently.a.payload).1))
  last : v 303 = some (.unary z.leaf.elected.unary.ctor
      (.leaf (m z.inspected.independently.b.payload).1))
  middle : v z.inspected.sourceRoot.span.center = some (.unary z.leaf.elected.unary.ctor
      (.leaf (m z.leaf.payload.capture.center).1))
  allVisible : z.inspected.inspected.hits = [z.leaf.elected.row]
  center : z.leaf.actual.center = z.leaf.payload.capture.center
  outputs : z.leaf.executed.fixed = []
  kids : z.leaf.executed.kids = []

inductive Meaning {contra : Bool} {x : Ordered contra} (z : FinishedRun x) (m : Assignment) (v : NativeViews) :
    Query → Nat → List Query → Prop where
  | root : Fits z.inspected.sourceRoot.world m v →
      z.inspected.sourceRoot.body.kids = [z.inspected.sourceRoot.occurrence] →
      Meaning z m v rootQuery z.inspected.sourceRoot.chosen.impl.id [childQuery z]
  | typed : NominalMeaning z m v → Meaning z m v (childQuery z) z.leaf.elected.row.id []

theorem local_nominal_sound {contra} {x : Ordered contra} (z : FinishedRun x)
    (started : run contra = some x) (m : Assignment) (v : NativeViews) (fit : Fits z.leaf.world m v) :
    ∀ d k kids,Local z d (.selected k kids) → Meaning z m v d k kids := by
  have prior : Fits z.inspected.sourceRoot.world m v :=
    ⟨restrict ((preserves_iff ..).mp z.leaf.retained) m fit.1,fit.2⟩
  have ends := exact_endpoint_provenance z.inspected.independently started m v prior
  have mid := independent_center_read_after_election z.leaf.payload m v prior
  intro _ _ _ chosen
  cases chosen with
  | root => exact .root prior z.inspected.sourceRoot.ordered
  | typed =>
    rw [← z.leaf.elected.positive] at ends
    exact .typed ⟨prior,ends.1,ends.2.1,mid,z.leaf.elected.alone,z.leaf.center,z.leaf.noWrites,z.leaf.noKids⟩

theorem nominal_tree_selected {contra} {x : Ordered contra} (z : FinishedRun x) :
    Classify (Local z) rootQuery
      (.selected (.node z.inspected.sourceRoot.chosen.impl.id [.node z.leaf.elected.row.id []])) := by
  refine ⟨.selected z.inspected.sourceRoot.chosen.impl.id [.selected z.leaf.elected.row.id []],?_,?_⟩
  · exact .selected .root (.cons (.selected .typed .nil) .nil)
  · exact .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem same_model_selected_nominal_dictionary {contra} {x : Ordered contra} (z : FinishedRun x)
    (started : run contra = some x) (m : Assignment) (v : NativeViews) (fit : Fits z.leaf.world m v) :
    Evidence (Meaning z m v) rootQuery (.node z.inspected.sourceRoot.chosen.impl.id [.node z.leaf.elected.row.id []]) :=
  dictionary_sound (local_nominal_sound z started m v fit) (nominal_tree_selected z)

end Yulang.GeneralDeclarativeWitnessNominalDictionary364
