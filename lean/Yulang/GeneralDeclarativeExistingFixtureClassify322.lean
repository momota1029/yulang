import Yulang.GeneralDeclarativeExistingFixtureProbe322
import Yulang.GeneralDeclarativeExistingFixtureGraph322
import Yulang.GeneralDeclarativeExistingFixtureRead322
import Yulang.GeneralDeclarativeExampleTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingFixtureClassify322
open GeneralDeclarativeExistingFixture322
open GeneralDeclarativeExistingFixtureProbe322 (readyRoot readyChild rootMatches childMatches)
open GeneralDeclarativeExistingFixtureGraph322 (no_cycle)
open GeneralDeclarativeExistingFixtureRead322 (rootBuilt childBuilt)
open GeneralDeclarativeExampleSource320 (registry interp root leaf checked)
open GeneralDeclarativeExampleRead320 (root_only)
open GeneralDeclarativeExampleTree320 (diagnostic dictionary completes)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Local Recurs)
open GeneralDeclarativeExistingLocal322 (Proven sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

def tested : Candidates :=
  ⟨HeadMatches (restriction supported) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction supported) registry.constructors interp d decl⟩

abbrev localRule := Local state registry interp supported tested (Proven state supported registry interp)

theorem no_recurs (d) : ¬Recurs state registry interp tested d := by
  rintro (⟨a,_,cycle⟩|⟨decl,_,index,a,pat,code,_,_,_,place,_,cycle⟩)
  · exact no_cycle a.lower cycle
  · exact no_cycle place cycle

theorem leaf_only (d) (yes : d ∈ registry.declarations) (role : d.role = child.role) : d = leaf := by
  rcases List.mem_cons.mp yes with rfl|later
  · cases role
  · exact List.mem_singleton.mp later

theorem parent_chosen : localRule root (.selected wrap.id [child]) := by
  refine .selected readyRoot (no_recurs _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,rootMatches⟩ ?_ rootBuilt
  · rintro ⟨decl,⟨visible,role⟩,unknown⟩
    have eq := root_only decl visible role
    subst decl
    exact unknown rootMatches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [root_only decl visible role]

theorem child_chosen : localRule child (.selected leaf.id []) := by
  refine .selected readyChild (no_recurs _) ?_
    ⟨⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩,childMatches⟩ ?_ childBuilt
  · rintro ⟨decl,⟨visible,role⟩,unknown⟩
    have eq := leaf_only decl visible role
    subst decl
    exact unknown childMatches
  · intro decl ⟨⟨visible,role⟩,_⟩
    rw [leaf_only decl visible role]

theorem resolves : Classify localRule root (.selected dictionary) :=
  ⟨diagnostic,.selected parent_chosen (.cons (.selected child_chosen .nil) .nil),completes⟩

theorem all_models (m : Assignment) (fits : Models state m) :
    Evidence registry interp m root dictionary :=
  sound checked m fits resolves

theorem inhabited : Models state model ∧ Evidence registry interp model root dictionary :=
  ⟨valid,all_models model valid⟩

abbrev actualRows : List Equation :=
  [⟨1,nominalCode (.variable 3)⟩,⟨8,.variable 3⟩,⟨9,.variable 3⟩,⟨10,.variable 3⟩,
   ⟨12,.variable 5⟩,⟨6,nominalCode (.variable 5)⟩]

/-- Four compiler equations use logical transitivity or compound
substitution; they were not textually present in this unchanged state. -/
theorem exact_rows_and_nonliteral :
    GeneralDeclarativeNodeFacts320.nodeFacts registry interp parentCapture wrap root [child] = some actualRows ∧
    ∀ row ∈ [⟨1,nominalCode (.variable 3)⟩,⟨9,.variable 3⟩,
      ⟨12,.variable 5⟩,⟨6,nominalCode (.variable 5)⟩], row ∉ state.equations := by
  refine ⟨rfl,?_⟩
  intro row listed
  simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl|rfl|rfl
  all_goals simp [state,equations,nominalCode,product]

end Yulang.GeneralDeclarativeExistingFixtureClassify322
