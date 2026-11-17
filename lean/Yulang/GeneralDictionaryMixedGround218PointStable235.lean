import Yulang.GeneralDictionaryMixedGround218PointRefresh235
import Yulang.GeneralNominalVersionedMixedEqualityClosure235
import Yulang.GeneralDictionaryGroundCopy218SaturatedState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
/-! Sufficient full mixed-kernel stability obligations for the concrete 218
three-site point stage. Root commitment and raw equality closure are explicit
remaining premises; this lemma alone is not a reachable Stable endpoint. -/
namespace Yulang.GeneralDictionaryMixedGround218PointStable235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (plan childSite model)
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
variable {state : State roles}

def Sites (state : State roles) : Prop :=
  state.core.sites = [plan.input,childSite,newChild] ∧
  state.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root,childSite.observed,newChild.observed] ∧
  state.core.erased.current.edges = [(root,childSite.occurrence),(root,newChild.occurrence)]

theorem generated_only (sites : Sites state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence := by
  induction generated with
  | root => exact Or.inl rfl
  | child prior member ih =>
    rw [sites.2.2] at member
    rcases List.mem_cons.mp member with same | member
    · exact Or.inr (Or.inl (congrArg Prod.snd same))
    · exact Or.inr (Or.inr (congrArg Prod.snd (List.mem_singleton.mp member)))
  | alias prior one two related ih =>
    rw [sites.2.1] at two
    rcases List.mem_cons.mp two with rfl | two
    · exact Or.inl rfl
    · rcases List.mem_cons.mp two with rfl | two
      · exact Or.inr (Or.inl rfl)
      · cases List.mem_singleton.mp two; exact Or.inr (Or.inr rfl)

theorem frame_old_input (sites : Sites state)
    (framed : GeneralNominalVersionedEvidence231.Frame registry state.core childSite.occurrence key candidate) :
    candidate.input = childSite := by
  have member := framed.center_recorded
  rw [sites.1] at member
  rcases List.mem_cons.mp member with first | member
  · have eq := candidate.input_exact.trans framed.occurrence_eq
    rw [first] at eq
    have role := congrArg (fun o => o.demand.role) eq
    cases role
  · rcases List.mem_cons.mp member with second | last
    · exact second
    · have eq := candidate.input_exact.trans framed.occurrence_eq
      rw [List.mem_singleton.mp last] at eq
      exact False.elim (GeneralDictionaryGroundCopy218Reinstall.different_child eq)

theorem no_install_old (sites : Sites state) (recorded : plan ∈ state.plans)
    (effect : Effect roles) (focus : effect.plan.packet.site.occurrence = childSite.occurrence) :
    ¬ Installable registry state effect := by
  intro enabled
  obtain ⟨given,valid,held,_⟩ := enabled.common
  have frame : GeneralNominalVersionedEvidence231.Frame registry state.core childSite.occurrence effect.plan.packet.declaration.id effect.plan := by
    rw [← focus,← enabled.registry_eq,← enabled.snapshot_eq]
    exact effect.frame
  have input := frame_old_input sites frame
  have declaration := GeneralDictionaryGroundCopy218Obstruction.role_leaf frame.visible frame.role_eq
  have queries : GeneralNominalInspection.queries effect.plan.packet.context.state effect.plan.packet.context.interpretation
      effect.plan.packet.declaration = [.variables [0],.variables [0]] := by
    rw [declaration]
    exact GeneralDictionaryGroundCopy218Obstruction.leaf_queries _
  have shared := GeneralNominalVersionedHeadSharing232.packet_holds effect.plan given held
  have one : (⟨0,.source (GeneralDictionaryTopLevelSharing217.firstCenter effect.plan.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ effect.plan.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,GeneralDictionaryTopLevelSharing217.firstCenter]
  have two : (⟨0,.source (GeneralDictionaryTopLevelSharing217.secondCenter effect.plan.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ effect.plan.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,GeneralDictionaryTopLevelSharing217.secondCenter]
  have same := (GeneralDictionaryHeadSharing220.holds_iff effect.plan given).mp shared _ one _ two rfl
  rw [input] at same
  exact GeneralDictionaryMixedGround218Obstruction234.centers_different given (valid.2.1 plan recorded) same

theorem new_pending (allocated reserved atoms)
    (current : state.core.erased.current.context.state =
      GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved atoms) :
    GeneralNominalState.RootPending state.core.erased.current.context.state newChild.occurrence.demand := by
  rw [current]
  refine ⟨⟨0,by decide⟩,?_⟩
  rw [GeneralDictionaryGroundCopy218Reinstall.child_arguments]
  change ¬ GeneralNominalState.Known (GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved atoms) 4
  rintro ⟨slot,sourceEq,head | ⟨descriptor,recorded⟩⟩
  · have equal : slot = (4 : Fin 8) := Fin.ext sourceEq
    subst slot
    exact head rfl
  · have equal : slot = (4 : Fin 8) := Fin.ext sourceEq
    subst slot
    cases recorded

theorem merges_closed (sites : Sites state)
    (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (same : SameInputs (Models state) first last) :
    GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity := by
  rw [sites.1] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
  all_goals first | exact .refl _ | have bad := same.1; cases bad

theorem stable (sites : Sites state) (recorded : plan ∈ state.plans)
    (allocated reserved atoms)
    (current : state.core.erased.current.context.state =
      GeneralDictionaryGroundCopy218Reobserve.pointExtended allocated reserved atoms)
    (valid : Models state model)
    (equalities : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed state)
    (root_committed : ∀ effect : Effect roles, Installable registry state effect →
      effect.plan.packet.site.occurrence = root → Committed state effect.plan) : Stable registry state root := by
  intro focus generated next action
  have location := generated_only sites generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      rw [sites.2.1] at absent
      rcases location with rfl | rfl | rfl
      · exact absent _ List.mem_cons_self rfl
      · exact absent _ (List.mem_cons_of_mem _ List.mem_cons_self) rfl
      · exact absent _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl
    | refresh context certificate identity member unknown known =>
      exact GeneralDictionaryMixedGround218PointRefresh235.no_refresh allocated reserved atoms current valid certificate unknown known
    | reobserve revision certificate improved =>
      have point : GeneralNominalReobservationSteps.PointClosed state.core.erased.current.context.state := by
        rw [current]; exact GeneralDictionaryGroundCopy218Reobserve.point_closed allocated reserved atoms
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point revision improved
    | equate first last one two equal novel => exact novel (equalities first last one two equal)
  | refresh focus context certificate identity member unknown known =>
    exact GeneralDictionaryMixedGround218PointRefresh235.no_refresh allocated reserved atoms current valid certificate unknown known
  | install effect enabled novel =>
    rcases location with parent | old | new
    · exact novel (root_committed effect enabled parent)
    · exact no_install_old sites recorded effect old enabled
    · exact enabled.safe.1 (new ▸ new_pending allocated reserved atoms current)
  | merge first last one two same novel => exact novel (merges_closed sites one two same)
end Yulang.GeneralDictionaryMixedGround218PointStable235
