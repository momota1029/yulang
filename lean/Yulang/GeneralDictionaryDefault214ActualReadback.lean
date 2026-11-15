import Yulang.GeneralDictionaryDefault214ActualSites
import Yulang.GeneralNominalCompleteNames183
import Yulang.GeneralNominalQueryProvenance183

/-! Corrected-journal head-origin producers. The producer is selected before
all model quantifiers, and total stored packet semantics supplies its equality.
No compatibility between this producer and a new candidate is asserted. -/
namespace Yulang.GeneralDictionaryDefault214ActualReadback
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralDictionaryDefaultDepth208 (frame)
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Unlike legacy actual producers, this relation uses only the head schema,
which is retained in corrected total packet semantics. -/
def Actual (state : State roles) (identity : Nat) (origin : Origin) : Prop :=
  ∃ plan ∈ state.core.plans, ∃ entry ∈ plan.headSchema.variables,
    entry.mode = .actual ∧ plan.binder entry.name = identity ∧ entry.origin = origin

theorem actual_same (valid : Models state model) (producer : Actual state identity origin) :
    GeneralNominalOriginTerms.Same model origin (.source identity) := by
  obtain ⟨plan,registered,entry,member,actual,rfl,rfl⟩ := producer
  exact GeneralNominalCenteredHeadMatPlans.capture_agreement
    (GeneralNominalCenteredHeadMatStepPackets.models_iff.mpr (valid.2.2.2.2.1 plan registered))
    entry member rfl actual

theorem registered_finished
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, Finished (headInspection plan) := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro previous member
      rcases List.mem_cons.mp member with rfl | old
      · have prepared := (frame enabled).prepared
        rw [← (frame enabled).context_eq] at prepared
        obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
        have equal : bounds = effect.plan.packet.bounds := Option.some.inj (found.symm.trans (frame enabled).located)
        subst bounds
        exact GeneralNominalInspectionAlignment.finished_origins effect.plan.packet.context.state _ effect.plan.packet.bounds _ _ 0 0 finished
      · exact ih previous old

theorem registered_input_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, Actual state (plan.binder name) origin := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 (registered_finished path plan registered) name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨origin,plan,registered,⟨captured.name,origin,.actual⟩,used,rfl,congrArg plan.binder equal,rfl⟩

theorem registered_capture_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, Actual state (plan.binder name) origin := by
  apply registered_input_actual path plan registered name
  rcases needed with named | ⟨clause,member,used⟩
  · exact named
  · exact plan.packet.checked.scope.1 clause member name used

theorem uniform_capture_readback
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, Actual state (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name)) := by
  obtain ⟨origin,witness⟩ := registered_capture_actual path plan registered name needed
  exact ⟨origin,witness,fun _ valid => actual_same valid witness⟩

theorem uniform_site_readback
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position) :
    ∃ origin, Actual state (site.center index) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (site.center index)) := by
  obtain ⟨plan,registered,name,needed,equal⟩ :=
    GeneralDictionaryDefault214ActualSites.purpose_eight_site_needed source path site member index center
  rw [← equal]
  exact uniform_capture_readback path plan registered name (Or.inr needed)

end Yulang.GeneralDictionaryDefault214ActualReadback
