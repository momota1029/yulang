import Yulang.GeneralDeclarativeEmissionFixture322
import Yulang.GeneralDeclarativeExistingFixtureGraph322
import Yulang.GeneralDeclarativeExistingFixtureProbe322
import Yulang.GeneralDeclarativeExampleTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionClassify322
open GeneralDeclarativeExistingFixture322 (state supported pointBounds model valid)
open GeneralDeclarativeExistingFixtureProbe322 (pairRow readyRoot rootMatches)
open GeneralDeclarativeExistingFixtureGraph322 (no_cycle)
open GeneralDeclarativeEmissionFixture322 (root_source leaf_source actual_names)
open GeneralDeclarativeExampleSource320 (registry interp root child leaf point checked)
open GeneralDeclarativeExampleRead320 (root_only leaf_only)
open GeneralDeclarativeExampleTree320 (diagnostic dictionary completes)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Ready knows_row)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Local Recurs)
open GeneralDeclarativeEmissionLocal322 (Generates source_sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

def tests : Candidates :=
  ⟨HeadMatches (restriction supported) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction supported) registry.constructors interp d decl⟩

abbrev localRule := Local state registry interp supported tests (Generates state supported registry interp)

theorem safe (d) : ¬Recurs state registry interp tests d := by
  rintro (⟨a,_,cycle⟩|⟨decl,_,index,a,pat,code,_,_,_,site,_,cycle⟩)
  · exact no_cycle a.lower cycle
  · exact no_cycle site cycle

theorem child_ready : Ready supported child := by
  intro arg fromSource
  cases List.mem_singleton.mp fromSource
  exact ⟨_,knows_row pairRow rfl⟩

theorem child_matches :
    HeadMatches (restriction supported) registry.constructors interp child leaf :=
  .cons ⟨pointBounds 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

theorem parent_select : localRule root (.selected wrap.id [child]) := by
  refine .selected readyRoot (safe _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,rootMatches⟩ ?_ root_source
  · rintro ⟨decl,⟨visible,role⟩,blocked⟩
    rw [root_only decl visible role] at blocked
    exact blocked rootMatches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [root_only decl visible role]

theorem child_select : localRule child (.selected leaf.id []) := by
  refine .selected child_ready (safe _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches⟩ ?_ leaf_source
  · rintro ⟨decl,⟨visible,role⟩,blocked⟩
    rw [leaf_only decl visible role] at blocked
    exact blocked child_matches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [leaf_only decl visible role]

theorem actual_source_tree : Classify localRule root (.selected dictionary) :=
  ⟨diagnostic,.selected parent_select (.cons (.selected child_select .nil) .nil),completes⟩

theorem actual_source_models (m : Assignment) (fits : Models state m) :
    Evidence registry interp m root dictionary :=
  source_sound checked m fits actual_source_tree

theorem actual_source_inhabited : Models state model ∧ Evidence registry interp model root dictionary :=
  ⟨valid,actual_source_models model valid⟩

end Yulang.GeneralDeclarativeEmissionClassify322
