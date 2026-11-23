import Yulang.GeneralDeclarativeWitnessOrderedDictionary363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 78000
set_option maxHeartbeats 98000000
namespace Yulang.GeneralDeclarativeWitnessSelectedSourceMeaning363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run payload)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (lo mid hi all_claims_one_final_fit)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (asked)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (Complete returned_model_has_prior_author_and_child_state)
open GeneralDeclarativeWitnessLocatedElection363 (election_not_called_from_compiler)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessRecordWidthFixture359 (receipt)
open GeneralDeclarativeWitnessRecordResidual359 (lowerSpine upperSpine authored_interval)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Frontier Classify)

structure Query where
  path : List Nat
  demand : Demand

def rootQuery : Query := ⟨[10],asked⟩
def later {contra x} (s : @Complete contra x) : Query := ⟨[10,0],s.parent.occurrence⟩

/-- Both local source decisions were made independently of their body
executions. These source-indexed rules keep the actual occurrence
path and exact child demand, including its ordinary aliases. -/
inductive Local {contra : Bool} {x : Ordered contra} (s : Complete x) : Query → Frontier Query → Prop where
  | root : Local s rootQuery (.selected s.parent.chosen.impl.id [later s])
  | child : Local s (later s) (.selected s.child.chosen.impl.id [])

def Reads (contra : Bool) (m : Assignment) (v : NativeViews) : Prop :=
  v 301 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 0)).1)) ∧
  v 302 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 1)).1)) ∧
  v 303 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 2)).1))

structure RootMeaning {contra : Bool} {x : Ordered contra} (s : Complete x)
    (m : Assignment) (v : NativeViews) : Prop where
  authored : s.parent.chosen.impl ∈ s.environment.source.declarations
  separate : Reads contra m v
  ordered1 : ContextDerives table m false (lo x) (mid x)
  ordered2 : ContextDerives table m false (mid x) (hi x)
  ordinaryLow : Equivalent (m 60).1 ((lowerSpine receipt).denote m)
  ordinaryHigh : Equivalent (m 62).1 ((upperSpine receipt).denote m)
  modeLeft : s.parent.ready.left.rows = s.parent.ready.nativeInput.left.rows
  modeRight : s.parent.ready.right.rows = s.parent.ready.nativeInput.right.rows
  chosenBody : s.parent.body.impl = s.parent.chosen.impl
  literalWhereList : s.parent.body.kids = [s.parent.occurrence]

structure ChildMeaning {contra : Bool} {x : Ordered contra} (s : Complete x)
    (m : Assignment) (v : NativeViews) : Prop where
  authored : s.child.chosen.impl ∈ s.environment.source.declarations
  prior : Fits s.parent.world m v
  separate : Reads contra m v
  actualCenter : s.child.binder.center = s.parent.span.center
  selectedBody : s.child.prepared.impl = s.child.chosen.impl
  outputs : s.child.body.fixed = []
  terminalList : s.child.body.kids = []

inductive Meaning {contra : Bool} {x : Ordered contra} (s : Complete x) (m : Assignment) (v : NativeViews) :
    Query → Nat → List Query → Prop where
  | root : RootMeaning s m v → Meaning s m v rootQuery s.parent.chosen.impl.id [later s]
  | child : ChildMeaning s m v → Meaning s m v (later s) s.child.chosen.impl.id []

theorem local_source_sound {contra} {x : Ordered contra} (s : Complete x)
    (made : run contra = some x) (m : Assignment) (v : NativeViews) (fit : Fits s.child.world m v) :
    ∀ d key children,Local s d (.selected key children) → Meaning s m v d key children := by
  obtain ⟨parent,origin⟩ := returned_model_has_prior_author_and_child_state s.child m v fit
  have typed := all_claims_one_final_fit made s.parent.ready.sourceCheck m v origin
  have plain := authored_interval s.parent.ready.recordInput m origin.1
  intro d k children h
  cases h with
  | root =>
    exact .root ⟨(election_not_called_from_compiler s.parent.chosen).1,typed.2.2,typed.1,typed.2.1,
      plain.1,plain.2.1,
      GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows s.parent.ready.nativeInput.left s.parent.ready.left,
      GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows s.parent.ready.nativeInput.right s.parent.ready.right,
      s.parent.actual,s.parent.ordered⟩
  | child =>
    exact .child ⟨(election_not_called_from_compiler s.child.chosen).1,parent,typed.2.2,s.child.center,
      s.child.actual,s.child.emptyOutput,s.child.doneChildren⟩

theorem actual_ordered_classification {contra} {x : Ordered contra} (s : Complete x) :
    Classify (Local s) rootQuery (.selected (.node s.parent.chosen.impl.id [.node s.child.chosen.impl.id []])) := by
  refine ⟨.selected s.parent.chosen.impl.id [.selected s.child.chosen.impl.id []],?_,?_⟩
  · exact .selected .root (.cons (.selected .child .nil) .nil)
  · exact .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem every_actual_selected_dictionary_same_model {contra} {x : Ordered contra} (s : Complete x)
    (made : run contra = some x) (m : Assignment) (v : NativeViews) (fit : Fits s.child.world m v)
    {d dict} (classified : Classify (Local s) d (.selected dict)) : Evidence (Meaning s m v) d dict :=
  GeneralDeclarativeWitnessOrderedDictionary363.dictionary_sound (local_source_sound s made m v fit) classified

end Yulang.GeneralDeclarativeWitnessSelectedSourceMeaning363
