import Yulang.GeneralVersionRebaseStep259
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionRebaseModels259
open GeneralRebaseStep258
open GeneralVersionRebaseStep259 (facts initialState finalState)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVersionLoopSource237 (snapshot F)
open GeneralDictionaryVersionLoopPacket237 (actual)
open GeneralVersionBoundaryCompletion259 (Agree complete)
open CommonNominalFullCarrier

def factHolds (assignment : Assignment) : Fact → Prop
 | .lower owner atom => owner = 0 ∧ atom = 0 ∧ Subtype (assignment 2).1 (assignment actual).1
 | .upper owner atom => owner = 0 ∧ atom = 0 ∧ Subtype (assignment actual).1 (assignment 2).1
 | .binder 0 => Subtype (assignment 2).1 (assignment actual).1
 | .binder 1 => Subtype (assignment actual).1 (assignment 2).1
 | .binder _ => False
 | .installed owner => owner = 0

def Models (state : State facts) (assignment : Assignment) : Prop :=
 GeneralNominalState.Models snapshot assignment ∧ ∀ fact ∈ present state, factHolds assignment fact

theorem initial_exact (assignment : Assignment) : Models initialState assignment ↔
 GeneralNominalState.Models snapshot assignment := by
 have empty : present initialState = [] := by decide
 simp only [Models,empty,List.not_mem_nil,false_implies,implies_true,and_true]

theorem final_exact (assignment : Assignment) : Models finalState assignment ↔
 GeneralNominalState.Models snapshot assignment ∧ Equivalent (assignment actual).1 (assignment 2).1 := by
 have full : present finalState = facts := by decide
 change (GeneralNominalState.Models snapshot assignment ∧ ∀ fact ∈ present finalState, factHolds assignment fact) ↔ _
 rw [full]
 constructor
 · rintro ⟨source,all⟩
   exact ⟨source,all (.binder 1) (by simp [facts]),all (.binder 0) (by simp [facts])⟩
 · rintro ⟨source,upper,lower⟩
   refine ⟨source,?_⟩
   intro fact member
   simp only [facts,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl
   · rfl
   · exact ⟨rfl,rfl,lower⟩
   · exact ⟨rfl,rfl,upper⟩
   · exact lower
   · exact upper

theorem completed_binder (boundary : Assignment)
 (valid : GeneralNominalState.Models snapshot boundary) :
 Equivalent (complete boundary actual).1 (complete boundary 2).1 := by
 have above : 3 < actual := GeneralNominalIdentities.source_above_seed ..
 have actualType : (complete boundary actual).1 = F := by
   simp only [complete,show ¬ actual ≤ 3 by omega,ite_false]
   exact GeneralDictionaryVersionLoopPacket237.actual_value
 rw [actualType, (GeneralVersionBoundaryCompletion259.agrees boundary).1 2 (by decide)]
 have foo := GeneralDictionaryVersionLoopInitial238.foo_fixed boundary valid
 exact ⟨foo.2,foo.1⟩

theorem completed (state : State facts) (boundary : Assignment)
 (valid : GeneralNominalState.Models snapshot boundary) : Models state (complete boundary) := by
 have source := (GeneralVersionPublicProjection259.source_agree (complete boundary) boundary
   (GeneralVersionBoundaryCompletion259.agrees boundary)).mpr valid
 have final := (final_exact (complete boundary)).mpr ⟨source,completed_binder boundary valid⟩
 refine ⟨source,?_⟩
 intro fact member
 have inBasis : fact ∈ facts := (List.mem_filter.mp member).1
 have inFinal : fact ∈ present finalState := by
   have full : present finalState = facts := by decide
   rw [full]; exact inBasis
 exact final.2 fact inFinal

theorem public_models (state : State facts) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models state assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact (GeneralVersionPublicProjection259.source_agree assignment boundary same).mp valid.1
 · intro valid
   exact ⟨complete boundary,GeneralVersionBoundaryCompletion259.agrees boundary,completed state boundary valid⟩
end Yulang.GeneralVersionRebaseModels259
