import Yulang.GeneralDeclarativeExampleFacts320
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 4300000
namespace Yulang.GeneralDeclarativeExampleUnsettled320
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeExampleSource320 (registry interp input child root capture state nApp int)
open GeneralDeclarativeExampleSource320 (leaf association leaf_checked)
open GeneralDeclarativeExampleRead320 (headExpr leaf_only)
open GeneralDeclarativeExampleFacts320 (rootFacts leafFacts root_batch)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Entails literal BatchRecipe)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeNormalized320 (Center center_sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent nominal subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)

def before : State := ⟨state.normal,
  [⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,⟨6,nApp 5⟩]⟩

def bad : Assignment := fun n =>
  (if n ≤ 2 then nominal 0 [.inl int] else if n = 6 then nominal 0 [.inl .top]
    else if n = 5 then .top else int,Common.rowEmpty)

theorem valid_before : Models before bad := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair found
    change pair ∈ [(0,1),(1,2)] at found
    rcases List.mem_cons.mp found with rfl|tail
    · exact subtype_refl _
    · cases List.mem_singleton.mp tail
      exact subtype_refl _
  · intro row found
    change row ∈ [⟨0,nApp 3⟩,⟨2,nApp 3⟩,⟨3,.primitive (.scalar .int) []⟩,⟨6,nApp 5⟩] at found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem missing_child_consequence : ¬ Entails before ⟨5,.variable 3⟩ := by
  intro forced
  have contradiction : Equivalent (.top : Ty) int := forced bad valid_before
  exact GeneralDeclarativeRepeat320.top_not_int contradiction.1

theorem not_all_child_facts : ¬ ∀ row ∈ leafFacts, Entails before row := by
  intro all
  exact missing_child_consequence (all _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem old_center (m : Assignment) (valid : Models before m) :
    Equivalent (m 1).1 (nominal 0 [.inl (m 3).1]) := by
  have bound : Bounds before input := GeneralDeclarativeExampleSource320.input_bounds
  have result : Center before capture input headExpr :=
    .endpoints bound (GeneralDeclarativePoint320.frozen_nominal before capture 0 [.variable 0])
      (.whole List.mem_cons_self) (.whole (List.mem_cons_of_mem _ List.mem_cons_self))
  exact center_sound result m valid

/-- The parent can have all its own generated equations already forced
while a requested result of the child is still unconstrained. -/
theorem parent_local : BatchRecipe before registry interp root wrap.id [child] := by
  refine ⟨wrap,capture,rootFacts,rfl,List.mem_cons_self,?_,?_,root_batch,?_⟩
  · intro n member
    change n ∈ [0] at member
    cases List.mem_singleton.mp member
    exact ⟨.refl _, .refl _⟩
  · intro arg member
    cases List.mem_singleton.mp member
    exact GeneralDeclarativeExampleSource320.input_bounds
  · intro row found
    simp only [rootFacts,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl
    · exact old_center
    · exact fun m _ => eqv_refl (m 3).1
    · exact fun m _ => eqv_refl (m 3).1
    · exact fun m _ => eqv_refl (m 3).1
    · exact fun m _ => eqv_refl (m 5).1
    · exact literal (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_singleton_self _))))

/-- The same ordinary state has a model which refutes even the child leaf's
dictionary. This refutes "selected parent means complete dictionary",
not the approved delayed selection policy. -/
theorem child_not_evidence : ¬ Evidence registry interp bad child (.node leaf.id []) := by
  intro cert
  cases cert with
  | node given _ =>
    obtain ⟨decl,cap,_,typed⟩ := given
    cases leaf_only decl typed.visible typed.role
    have head := GeneralDeclarativeNamedTree320.position typed.head
      (show child.arguments[0]? = some (GeneralDeclarativeExampleSource320.point 3) from rfl)
      (show leaf.head[0]? = some (.var 0) from rfl)
    have actual : Equivalent int (bad (cap 0).center).1 := head.1
    obtain ⟨body,prov,eq⟩ := typed.outputs ⟨1,5⟩ List.mem_cons_self
    cases prov with
    | explicit equation present _ =>
      cases List.mem_singleton.mp present
      have returned : Equivalent (.top : Ty) (bad (cap 0).center).1 := eq
      exact GeneralDeclarativeRepeat320.top_not_int (eqv_trans returned (eqv_symm actual)).1
    | default rhs _ impossible =>
      change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
      cases Option.some.inj impossible

end Yulang.GeneralDeclarativeExampleUnsettled320
