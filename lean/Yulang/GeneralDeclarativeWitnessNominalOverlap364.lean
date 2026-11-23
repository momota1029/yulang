import Yulang.GeneralDeclarativeWitnessNominalDictionaryModel364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 92000
set_option maxHeartbeats 128000000
namespace Yulang.GeneralDeclarativeWitnessNominalOverlap364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessNonpointPort362 (receiver)
open GeneralDeclarativeWitnessThreeNative362 (ctor)
open GeneralDeclarativeWitnessActualCompoundElection364 (Read check compound)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Query rootQuery)
open GeneralDeclarativeWitnessElectedPayload364 (elect key)
open GeneralDeclarativeWitnessOrderedDictionary363 (dictionary_sound)
open CommonRoleOutermostResolver (Frontier Classify)
open GeneralDeclarations (Declaration)

structure Found {contra : Bool} (x : Ordered contra) where
  tested : Read x
  exact : tested.inspected.hits = [receiver,compound (ctor contra)]

def actual {contra} (x : Ordered contra) : Option (Found x) := do
  let tested ← check x [receiver,compound (ctor contra)]
  if exact : tested.inspected.hits = [receiver,compound (ctor contra)] then
    pure ⟨tested,exact⟩
  else none

theorem overlap_exists_for_either_declared_direction (contra : Bool) :
    ((run contra).map fun x => (actual x).isSome).getD false = true := by cases contra <;> decide +kernel

def whereQuery {contra x} (s : @Found contra x) : Query := ⟨[10,0],s.tested.sourceRoot.occurrence⟩

inductive Local {contra : Bool} {x : Ordered contra} (s : Found x) : Query → Frontier Query → Prop where
  | root : Local s rootQuery (.selected s.tested.sourceRoot.chosen.impl.id [whereQuery s])
  | both : Local s (whereQuery s) .ambiguous

theorem real_compound_rival_affects_parent {contra} {x : Ordered contra} (s : Found x) :
    Classify (Local s) rootQuery .ambiguous := by
  refine ⟨.selected s.tested.sourceRoot.chosen.impl.id [.ambiguous],?_,?_⟩
  · exact .selected .root (.cons (.ambiguous .both) .nil)
  · exact .selected (.cons .ambiguous .nil) (.ambiguous (by simp) (by simp))

theorem cannot_elect_through_two_exact_hits {contra} {x : Ordered contra} (s : Found x) :
    (elect s.tested key).isNone = true := by
  unfold elect
  simp [s.exact]

end Yulang.GeneralDeclarativeWitnessNominalOverlap364
