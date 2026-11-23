import Yulang.GeneralDeclarativeWitnessTwoActualChildren363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 84000
set_option maxHeartbeats 108000000
namespace Yulang.GeneralDeclarativeWitnessTwoChildDictionary363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (lo mid hi all_claims_one_final_fit)
open GeneralDeclarativeWitnessBackedNativeInput363 (source_evidence_agrees_in_every_model)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativePreparation360 (same_model_of_prepared)
open GeneralDeclarativeWitnessLocatedElection363 (election_not_called_from_compiler)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Query rootQuery Reads)
open GeneralDeclarativeWitnessTwoActualChildren363 (Pair build checked Leaf f1 f2)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence dictionary_sound)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Classify)

def leftSlot {contra x} (p : @Pair contra x) : Query := ⟨[10,0],p.first⟩
def rightSlot {contra x} (p : @Pair contra x) : Query := ⟨[10,1],p.second⟩

inductive Local {contra : Bool} {x : Ordered contra} (p : Pair x) : Query → Frontier Query → Prop where
  | parent : Local p rootQuery (.selected p.chosen.impl.id [leftSlot p,rightSlot p])
  | left : Local p (leftSlot p) (.selected p.a.chosen.impl.id [])
  | right : Local p (rightSlot p) (.selected p.b.chosen.impl.id [])

structure RootFact {contra : Bool} {x : Ordered contra} (p : Pair x)
    (m : Assignment) (v : NativeViews) : Prop where
  source : p.chosen.impl ∈ p.env.source.declarations
  three : Reads contra m v
  loEdge : ContextDerives table m false (lo x) (mid x)
  hiEdge : ContextDerives table m false (mid x) (hi x)
  exactOrder : p.body.kids = [p.first,p.second]

structure LeafFact {e w d f port} (r : Leaf e w d f port)
    (m : Assignment) (v : NativeViews) : Prop where
  source : r.chosen.impl ∈ e.source.declarations
  previous : Fits w m v
  own : Fits r.world m v
  center : r.bound.center = port.center
  outputs : r.body.fixed = []
  children : r.body.kids = []

inductive Meaning {contra : Bool} {x : Ordered contra} (p : Pair x) (m : Assignment) (v : NativeViews) :
    Query → Nat → List Query → Prop where
  | parent : RootFact p m v → Meaning p m v rootQuery p.chosen.impl.id [leftSlot p,rightSlot p]
  | left : LeafFact p.a m v → Meaning p m v (leftSlot p) p.a.chosen.impl.id []
  | right : LeafFact p.b m v → Meaning p m v (rightSlot p) p.b.chosen.impl.id []

theorem successive_real_states_have_one_model {contra} {x : Ordered contra} (p : Pair x)
    (made : run contra = some x) (m : Assignment) (v : NativeViews) (final : Fits p.b.world m v) :
    ∀ d k children,Local p d (.selected k children) → Meaning p m v d k children := by
  have mid := p.b.prior m v final
  have first := p.a.prior m v mid
  have origin : Fits x.after.final m v :=
    ⟨(same_model_of_prepared p.body m first.1).1,first.2⟩
  have compared := all_claims_one_final_fit made p.ready.sourceCheck m v origin
  intro _ _ _ localRule
  cases localRule with
  | parent => exact .parent ⟨(election_not_called_from_compiler p.chosen).1,
      compared.2.2,compared.1,compared.2.1,p.ordered⟩
  | left => exact .left ⟨(election_not_called_from_compiler p.a.chosen).1,first,mid,p.a.centered,p.a.noWrites,p.a.noKids⟩
  | right => exact .right ⟨(election_not_called_from_compiler p.b.chosen).1,mid,final,p.b.centered,p.b.noWrites,p.b.noKids⟩

theorem actual_ordered_sibling_dict {contra} {x : Ordered contra} (p : Pair x) :
    Classify (Local p) rootQuery (.selected (.node p.chosen.impl.id
      [.node p.a.chosen.impl.id [],.node p.b.chosen.impl.id []])) := by
  refine ⟨.selected p.chosen.impl.id [.selected p.a.chosen.impl.id [],.selected p.b.chosen.impl.id []],?_,?_⟩
  · exact .selected .parent (.cons (.selected .left .nil) (.cons (.selected .right .nil) .nil))
  · exact .selected (.cons (.selected .nil (.selected rfl))
      (.cons (.selected .nil (.selected rfl)) .nil)) (.selected rfl)

theorem actual_sibling_dict_same_model {contra} {x : Ordered contra} (p : Pair x)
    (made : run contra = some x) (m : Assignment) (v : NativeViews) (fit : Fits p.b.world m v) :
    Evidence (Meaning p m v) rootQuery (.node p.chosen.impl.id
      [.node p.a.chosen.impl.id [],.node p.b.chosen.impl.id []]) :=
  dictionary_sound (successive_real_states_have_one_model p made m v fit) (actual_ordered_sibling_dict p)

end Yulang.GeneralDeclarativeWitnessTwoChildDictionary363
