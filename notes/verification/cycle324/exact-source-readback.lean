import Yulang.GeneralDeclarativeHiddenPath324
import Yulang.GeneralDeclarativeRivalResolve324
import Yulang.GeneralDeclarativeErasureRegression324
import Yulang.GeneralDeclarativeFollowerDerived324
import Yulang.GeneralDeclarativeNFClassify324
import Yulang.GeneralDeclarativeRuleSequence324

open Yulang

example : GeneralDeclarativeAggregateFixture324.merged = ⟨33,3,34⟩ :=
  GeneralDeclarativeAggregateFixture324.computed

#check @GeneralDeclarativeHiddenState324.exact_child
#check @GeneralDeclarativeHiddenPath324.parent_event
#check @GeneralDeclarativeHiddenPath324.child_event
#check @GeneralDeclarativeHiddenPath324.full_source_path
#check @GeneralDeclarativeAggregateFixture324.exact_child
#check @GeneralDeclarativeRivalResolve324.rival_eliminated
#check @GeneralDeclarativeRivalResolve324.successful_with_rival
#check @GeneralDeclarativeErasureRegression324.whole_normal_batch
#check @GeneralDeclarativeFollowerDerived324.final_transition
#check @GeneralDeclarativeNFClassify324.sound
#check @GeneralDeclarativeRuleSequence324.replay_sound

open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeRuleSequence324 (AppliesInOrder Occurrence replay_sound)
open GeneralDeclarativeReobserve324 (Reobserves)
open GeneralDeclarativeNFClassify324 (Rule)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarativeEvidence320 (Evidence)

/-- Independently compose the two new proofs. Only the indicated
application/reobservation coverage remains as an external assumption. -/
theorem conditional_dictionary
    (checked : Checked r)
    (sequence : AppliesInOrder r i choices s frames t)
    (coverage : ∀ d impl names place, impl ∈ r.declarations →
      impl.role = d.role →
      Rule t r i support tests d
        (.selected impl.id (GeneralDeclarativeEmissionForest322.children impl names place)) →
      GeneralDeclarativeNFComplete324.ReadBack t r i d impl names place →
      ∃ old, (⟨d,impl,old⟩ : Occurrence) ∈ frames ∧ Reobserves t impl old names.input)
    (asked : Declared r d) (m_ok : Models t m)
    (selected : Classify (Rule t r i support tests) d (.selected dict)) :
    Evidence r i m d dict := by
  apply GeneralDeclarativeNFClassify324.sound checked ?_ asked m_ok selected
  rintro eq ⟨d,impl,names,place,decl,role,won,reads,justified⟩
  rcases coverage d impl names place decl role won reads with ⟨old,visited,current⟩
  exact replay_sound checked sequence visited decl current eq justified

#print axioms conditional_dictionary
