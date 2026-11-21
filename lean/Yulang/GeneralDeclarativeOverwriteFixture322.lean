import Yulang.GeneralDeclarativeRefuseOverwrite322
import Yulang.GeneralDeclarativeExistingFixtureClassify322
import Yulang.GeneralNominalBranchingReadback

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOverwriteFixture322
open GeneralDeclarativeExistingFixture322
open GeneralDeclarativeExistingFixtureClassify322 (leaf_only)
open GeneralDeclarativeExampleSource320 (registry interp leaf association)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds appendFacts)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeFootprint321 (equationNames stateNames)
open GeneralDeclarativeRefuseOverwrite322 (not_conservative no_ordinary_proof_when_model_fails)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl)
open GeneralNominalBranchingReadback (scalar_not_pair)

def loose : State := ⟨state.normal,equations.filter (fun row => row.left != 12)⟩
def bad : Assignment := fun name => if name = 12 then (.base .int,Common.rowEmpty) else model name
abbrev requested : Equation := ⟨12,.variable 5⟩

theorem old_model : Models loose bad := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pr found
    change pr ∈ [(0,1),(1,2),(8,9),(9,10)] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro row used
    change row ∈ equations.filter (fun eqn => eqn.left != 12) at used
    obtain ⟨seen,notTarget⟩ := List.mem_filter.mp used
    simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact eqv_refl _ | cases notTarget

theorem bad_result : ¬Holds bad requested :=
  fun eq => scalar_not_pair .int (.base .int) .top eq.1

theorem no_current_return : ¬Derives loose (.variable 12) (.variable 5) :=
  no_ordinary_proof_when_model_fails old_model bad_result

theorem no_rebind_with_extra_rows (rows : List Equation)
    (addTarget : requested ∈ rows) :
    ¬∃ m, Models (appendFacts loose rows) m ∧
      ∀ n ∈ stateNames loose ++ [12,5], m n = bad n := by
  apply not_conservative addTarget bad_result
  intro n seen
  exact List.mem_append_right _ seen

theorem no_child_dictionary : ¬Evidence registry interp bad child (.node leaf.id []) := by
  intro selected
  cases selected with
  | node typed _ =>
    obtain ⟨impl,cap,_,node⟩ := typed
    cases leaf_only impl node.visible node.role
    have literalHead := GeneralDeclarativeNamedTree320.position node.head
      (show child.arguments[0]? = some frame from rfl)
      (show leaf.head[0]? = some (.var 0) from rfl)
    have shape : Equivalent productType (bad (cap 0).center).1 := literalHead.1
    obtain ⟨body,chosen,out⟩ := node.outputs ⟨1,12⟩ List.mem_cons_self
    cases chosen with
    | explicit eq member _ =>
      cases List.mem_singleton.mp member
      have body : Equivalent (.base .int : Ty) (bad (cap 0).center).1 := out
      exact scalar_not_pair .int (.base .int) .top (eqv_trans body (eqv_symm shape)).1
    | default rhs _ impossible =>
      change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
      cases Option.some.inj impossible

end Yulang.GeneralDeclarativeOverwriteFixture322
