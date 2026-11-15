import Yulang.GeneralNominalCenteredHeadMatPermutationInstall
import Yulang.GeneralDictionaryDefaultKernel208

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultSimulation208
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalCenteredHeadMatPermutationAdministrative
open GeneralNominalCenteredHeadMatPermutationInstall
variable {roles : Roles.RoleDecls} {before after first last next : State roles} {root focus : Occurrence roles}

def Recorded (state : State roles) : Prop :=
  (∀ plan ∈ state.core.plans, GeneralNominalCenteredHeadMatStepKernel.Committed state plan) ∧
  ∀ plan ∈ state.core.plans, ∃ effect ∈ state.effects, effect.plan = plan

theorem full_committed (recorded : Recorded state) (member : plan ∈ state.core.plans) : Committed state plan := by
  obtain ⟨effect,present,same⟩ := recorded.2 plan member
  refine ⟨recorded.1 plan member,?_⟩
  intro model valid
  apply GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr
  refine ⟨((recorded.1 plan member).1 model valid).2.2,?_⟩
  exact same ▸ (valid.2.2.2.2.2 effect present).2

theorem full_committed_related (same : Related relation first last)
    (pair : GeneralNominalCenteredHeadMatPermutationPlans.Pair plan other) :
    Committed first plan ↔ Committed last other := by
  have old := GeneralNominalCenteredHeadMatPermutationInstall.committed same pair
  have rootEq := congrArg GeneralNominalDemandMerging.Site.occurrence pair.matched.packet.site
  have effects (model) :
      GeneralNominalCenteredHeadMatEffects.ClassEffects first.core plan.packet.site.occurrence plan model ↔
      GeneralNominalCenteredHeadMatEffects.ClassEffects last.core other.packet.site.occurrence other model := by
    rw [pair.effects,rootEq]
    exact same.core.snapshot.effects _ _ _
  constructor
  · intro before
    have after := old.mp before.1
    refine ⟨after,fun model valid => GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr
      ⟨(after.1 model valid).2.2,?_⟩⟩
    exact (effects model).mp (committed_class before ((same.models model).mpr valid))
  · intro after
    have before := old.mpr after.1
    refine ⟨before,fun model valid => GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr
      ⟨(before.1 model valid).2.2,?_⟩⟩
    exact (effects model).mpr (committed_class after ((same.models model).mp valid))

def Corresponds (first last : State roles) : Prop :=
  ∃ relation, Related relation first last ∧ Recorded first ∧ Recorded last

theorem corresponds_symm (same : Corresponds first last) : Corresponds last first := by
  obtain ⟨relation,paired,one,two⟩ := same
  exact ⟨_,paired.symm,two,one⟩

theorem packet_at (action : At registry before focus after) (member : packet ∈ before.core.erased.current.packets) :
    packet ∈ after.core.erased.current.packets := by
  cases action with
  | administrative action => cases action <;> exact member
  | refresh => exact member
  | merge => exact member
  | install => exact List.mem_cons_of_mem _ member

theorem edge_at (action : At registry before focus after) (member : edge ∈ before.core.erased.current.edges) :
    edge ∈ after.core.erased.current.edges := by
  cases action with
  | administrative action => cases action <;> exact member
  | refresh => exact member
  | merge => exact member
  | install => exact List.mem_append_left _ member

theorem recorded_at (recorded : Recorded before) (action : At registry before focus after) : Recorded after := by
  have retain {plan} (valid : GeneralNominalCenteredHeadMatStepKernel.Committed before plan) :
      GeneralNominalCenteredHeadMatStepKernel.Committed after plan :=
    ⟨fun model models => valid.1 model (stepModels (root := focus) ⟨focus,.root,action⟩ models),
      fun child member => edge_at action (valid.2 child member)⟩
  constructor
  · intro plan member
    cases action with
    | administrative action => apply retain; cases action <;> exact recorded.1 plan member
    | refresh => exact retain (recorded.1 plan member)
    | merge => exact retain (recorded.1 plan member)
    | install effect enabled novel =>
      rcases List.mem_cons.mp member with rfl | member
      · exact (installed_committed enabled.snapshot_eq).1
      · exact retain (recorded.1 plan member)
  · intro plan member
    cases action with
    | administrative action => cases action <;> exact recorded.2 plan member
    | refresh | merge => exact recorded.2 plan member
    | install effect enabled novel =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨effect,List.mem_cons_self,rfl⟩
      · obtain ⟨prior,present,same⟩ := recorded.2 plan member
        exact ⟨prior,List.mem_cons_of_mem _ present,same⟩

theorem at_forward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (action : At registry first focus next) :
    ∃ other, At otherRegistry last focus other ∧ Corresponds next other := by
  obtain ⟨relation,paired,recordedFirst,recordedLast⟩ := same
  have finish {other next} (one : At registry first focus next) (two : At otherRegistry last focus other)
      {relation} (nextPair : Related relation next other) : Corresponds next other :=
    ⟨relation,nextPair,recorded_at recordedFirst one,recorded_at recordedLast two⟩
  cases action with
  | administrative action =>
      obtain ⟨other,otherAction,nextPair⟩ := administrative paired action
      exact ⟨other,.administrative otherAction,finish (.administrative action) (.administrative otherAction) nextPair⟩
  | refresh focus context certificate source member unknown known =>
      have otherAction : At otherRegistry last focus (refresh last context) :=
        .refresh focus context (refresh_certificate paired certificate) source
          ((GeneralNominalMetadataEquivalence.sources paired.core.current.context.state source).mp member)
          (fun present => unknown ((GeneralNominalMetadataEquivalence.known paired.core.current.context.state source).mpr present)) known
      exact ⟨_,otherAction,finish (.refresh focus context certificate source member unknown known) otherAction
        (refresh_related paired context)⟩
  | merge one two recordedOne recordedTwo inputs novel =>
      have models := funext (fun model => propext (paired.models model))
      have otherAction : At otherRegistry last one.occurrence (merge last one two) :=
        .merge one two ((paired.core.centers _).mp recordedOne) ((paired.core.centers _).mp recordedTwo)
          (models ▸ inputs) (fun alias => novel ((paired.core.current.alias _ _).mpr alias))
      exact ⟨_,otherAction,finish (.merge one two recordedOne recordedTwo inputs novel) otherAction (merging paired one two)⟩
  | install effect enabled novel =>
      obtain ⟨other,enabledOther,matchPlan,snapshot⟩ := counterpart_enabled paired order roleEq enabled
      have novelOther := fun done => novel ((full_committed_related paired matchPlan).mpr done)
      have oneNew : effect.plan ∉ first.core.plans := fun member => novel (full_committed recordedFirst member)
      have twoNew : other.plan ∉ last.core.plans := fun member => novelOther (full_committed recordedLast member)
      have nextPair := installed_related paired enabled.snapshot_eq snapshot matchPlan oneNew twoNew
      have otherAction : At otherRegistry last effect.plan.packet.site.occurrence (install last other) :=
        matchPlan.matched.packet.site ▸ At.install other enabledOther novelOther
      exact ⟨_,otherAction,finish (.install effect enabled novel) otherAction nextPair⟩

theorem step_forward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (step : Step registry root first next) :
    ∃ other, Step otherRegistry root last other ∧ Corresponds next other := by
  obtain ⟨focus,generated,action⟩ := step
  obtain ⟨other,nextAction,paired⟩ := at_forward order roleEq same action
  obtain ⟨_,before,_,_⟩ := same
  exact ⟨other,⟨focus,(before.core.current.generated root focus).mp generated,nextAction⟩,paired⟩

theorem step_backward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (step : Step otherRegistry root last next) :
    ∃ other, Step registry root first other ∧ Corresponds other next := by
  obtain ⟨other,step,paired⟩ := step_forward (GeneralRegistryChildOrder.reorders_symm order)
    (order.2.1.symm.trans roleEq) (corresponds_symm same) step
  exact ⟨other,step,corresponds_symm paired⟩

theorem observations (same : Corresponds first last) (registry : Registry) (roleEq : registry.roles = roles) (demand frontier) :
    GeneralNominalCenteredHeadMatStepBoundary.Local registry first demand frontier ↔
      GeneralNominalCenteredHeadMatStepBoundary.Local registry last demand frontier := by
  obtain ⟨_,paired,_,_⟩ := same
  exact GeneralNominalCenteredHeadMatStepBoundary.local_iff.trans
    ((GeneralNominalCenteredHeadMatPermutationLocal.local_iff paired registry roleEq demand frontier).trans
      GeneralNominalCenteredHeadMatStepBoundary.local_iff.symm)

theorem steps_backward (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (path : B4Target.Steps (Step otherRegistry root) last final) :
    ∃ result, B4Target.Steps (Step registry root) first result ∧ Corresponds result final := by
  induction path with
  | refl => exact ⟨first,.refl,same⟩
  | tail _ step ih =>
      obtain ⟨previous,trace,paired⟩ := ih
      obtain ⟨next,edge,nextPair⟩ := step_backward order roleEq paired step
      exact ⟨next,.tail trace edge,nextPair⟩

theorem halt_reflects (order : Reorders registry otherRegistry) (roleEq : registry.roles = roles)
    (same : Corresponds first last) (halted : ∀ next, ¬ Step otherRegistry root last next) :
    ∀ next, ¬ Step registry root first next := by
  intro next step
  obtain ⟨other,edge,_⟩ := step_forward order roleEq same step
  exact halted other edge

theorem packet_free_ledgers (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : state.core.erased.current.packets = []) : state.core.plans = [] ∧ state.effects = [] := by
  induction path with
  | refl => exact ⟨rfl,rfl⟩
  | tail path step ih =>
      obtain ⟨focus,_,action⟩ := step
      have prior : _ := ih (List.eq_nil_iff_forall_not_mem.mpr (fun packet member => by
        have retained := packet_at action member
        rw [empty] at retained
        cases retained))
      cases action with
      | administrative action => cases action <;> exact prior
      | refresh => exact prior
      | merge => exact prior
      | install => cases empty

theorem packet_free_self (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : state.core.erased.current.packets = []) : Corresponds state state := by
  obtain ⟨plans,effects⟩ := packet_free_ledgers path empty
  refine ⟨fun _ _ => False,⟨Core.refl _,⟨(by intro _ _ _ impossible; cases impossible),
    (by intro _ _ _ impossible; cases impossible)⟩,(by intro _ _ impossible; cases impossible),?_,?_,?_,?_⟩,?_,?_⟩
  · rw [plans]; exact .nil
  · rw [effects]; exact .nil
  · intro plan member; rw [plans] at member; cases member
  · intro plan member; rw [plans] at member; cases member
  · constructor <;> intro plan member <;> rw [plans] at member <;> cases member
  · constructor <;> intro plan member <;> rw [plans] at member <;> cases member

theorem packet_free_steps (path : B4Target.Steps (Step registry root) start state)
    (empty : state.core.erased.current.packets = []) (otherRegistry) :
    B4Target.Steps (Step otherRegistry root) start state := by
  induction path with
  | refl => exact .refl
  | tail path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      have prior := ih (List.eq_nil_iff_forall_not_mem.mpr (fun packet member => by
        have retained := packet_at action member
        rw [empty] at retained
        cases retained))
      refine .tail prior ⟨focus,generated,?_⟩
      cases action with
      | administrative action => exact .administrative action
      | refresh focus context certificate source member unknown known => exact .refresh focus context certificate source member unknown known
      | merge one two a b inputs novel => exact .merge one two a b inputs novel
      | install => cases empty

end Yulang.GeneralDictionaryDefaultSimulation208
