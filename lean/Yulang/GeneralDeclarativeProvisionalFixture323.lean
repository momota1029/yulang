import Yulang.GeneralDeclarativeEmissionClassify322
import Yulang.GeneralDeclarativeOutputExact323
import Yulang.GeneralNominalBranchingReadback

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProvisionalFixture323
open GeneralDeclarativeExistingFixture322 (state equations productType nominalCode model supported inputOnly)
open GeneralDeclarativeExistingFixtureGraph322 (no_cycle)
open GeneralDeclarativeEmissionFixture322 (names place actual_names)
open GeneralDeclarativeExampleSource320 (root child input registry interp leaf point association checked)
open GeneralDeclarativeExampleRead320 (root_only leaf_only)
open GeneralDeclarationExamples (wrap outDefinition)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias Ready knows_row alias_refl)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs Local)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open CommonNominalFullCarrier (Ty nominal Equivalent subtype_refl)
open GeneralNominalBranchingReadback (scalar_not_pair)
open CommonRoleOutermostResolver (Classify All₂)

abbrev row : Equation := ⟨5,.variable 3⟩
def before : State := ⟨state.normal,equations.filter (fun eq => eq.left != 5)⟩
def countermodel : Assignment := fun n =>
  if n = 5 ∨ n = 12 ∨ n = 13 ∨ n = 15 then (.base .int,Common.rowEmpty)
  else if n = 6 ∨ n = 14 then (nominal 0 [.inl (.base .int)],Common.rowEmpty)
  else model n

theorem subsetOrdinary : before.equations ⊆ state.equations :=
  fun _ found => (List.mem_filter.mp found).1

def inputSupport : Supported before (fun _ => False) :=
  ⟨fun e origin => e ∈ before.equations ∧ origin = .source ∧ inputOnly e.left,fun h => h.1⟩

theorem before_model : Models before countermodel := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro p found
    change p ∈ [(0,1),(1,2),(8,9),(9,10)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro eq known
    obtain ⟨found,notCut⟩ := List.mem_filter.mp known
    change eq ∈ equations at found
    simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact eqv_refl _ | cases notCut

theorem not_output : ¬Holds countermodel row :=
  fun bad => scalar_not_pair .int (.base .int) .top bad.1

theorem fixedVarying : ¬Entails before row :=
  fun all => not_output (all _ before_model)

theorem no_cycle_before (name : Nat) : ¬AliasCycle before (observed before) name := by
  apply GeneralDeclarativeRank321.graph_no_cycle (GeneralDeclarativeExistingFixtureGraph322.weight)
  · intro a b known
    exact GeneralDeclarativeExistingFixtureGraph322.alias_weight a b
      (GeneralDeclarativeLowerKnown321.alias_mono (s := before) (t := state) rfl subsetOrdinary known)
  · intro a tagged b sight there
    obtain ⟨code,present,shape⟩ := sight
    exact GeneralDeclarativeExistingFixtureGraph322.shape_weight a tagged b
      ⟨code,subsetOrdinary present,shape⟩ there

theorem supported_row (n : Nat) (e : Expr) (contains : (⟨n,e⟩ : Equation) ∈ equations)
    (different : n ≠ 5) (input : inputOnly n) :
    (⟨n,e⟩ : Equation) ∈ (restriction inputSupport).equations :=
  from_source inputSupport ⟨List.mem_filter.mpr ⟨contains,by simpa using different⟩,rfl,input⟩

theorem bottom : (⟨0,nominalCode (.variable 3)⟩ : Equation) ∈ (restriction inputSupport).equations :=
  supported_row 0 _ (by simp [equations]) (by decide +kernel) (by simp [inputOnly])

theorem top : (⟨2,nominalCode (.variable 4)⟩ : Equation) ∈ (restriction inputSupport).equations :=
  supported_row 2 _ (by simp [equations]) (by decide +kernel) (by simp [inputOnly])

theorem pair : (⟨3,GeneralDeclarativeExistingFixture322.product⟩ : Equation) ∈
    (restriction inputSupport).equations :=
  supported_row 3 _ (by simp [equations]) (by decide +kernel) (by simp [inputOnly])

theorem readyRoot : Ready inputSupport root := by
  intro a found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_row bottom rfl⟩

theorem readyChild : Ready inputSupport child := by
  intro a found
  cases List.mem_singleton.mp found
  exact ⟨_,knows_row pair rfl⟩

def test : Candidates :=
  ⟨HeadMatches (restriction inputSupport) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction inputSupport) registry.constructors interp d decl⟩

theorem no_recurs (d) : ¬Recurs before registry interp test d := by
  rintro (⟨a,_,cycle⟩|⟨decl,_,i,a,pat,code,_,_,_,site,_,cycle⟩)
  · exact no_cycle_before a.lower cycle
  · exact no_cycle_before site cycle

theorem root_matches : test.viable root wrap := by
  refine .cons ⟨GeneralDeclarativeExistingFixture322.rootBounds, .nominal 0 [.variable 0], [⟨0,.actual,3⟩],[⟨0,.actual,4⟩],rfl,?_,?_⟩ .nil
  · exact .nominal (args := [3]) (alias_refl _) bottom (.cons .capture .nil)
  · exact .nominal (args := [4]) (alias_refl _) top (.cons .capture .nil)

theorem leaf_matches : test.viable child leaf :=
  .cons ⟨⟨.refl _,.refl _⟩,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

end Yulang.GeneralDeclarativeProvisionalFixture323
