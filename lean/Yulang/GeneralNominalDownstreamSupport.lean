import Yulang.GeneralNominalSupportChoices
import Yulang.GeneralNominalFeedbackSteps

/-! Alternative-sensitive downstream output support. Dependencies include
uninstalled generated requests and journal-certified observations before a
refresh is taken. Waiting paths include aliases and stop at discharge. A provisional
output can be used through a well-founded justification; discharge cuts the branch.
Unknown heads contribute no dependency. The full journal is never filtered. -/
namespace Yulang.GeneralNominalDownstreamSupport

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportChoices
open GeneralNominalRecursiveInspection (Test)

/-- Every stored fact is enabled in this slice, including named equalities. -/
def Available (state : Tracked roles) (identity : Nat) (test : Test) : Prop :=
  HeadSupported state (dependencyPool state) identity test

theorem pool_exact (state : Tracked roles) (model : GeneralNominalCommonBridge.Assignment) :
    Slice state (dependencyPool state) model ↔ AllModels state model := by
  constructor
  · intro valid
    exact ⟨valid.1,fun fact member => valid.2 fact member
      (fun _ dependency => List.mem_flatMap.mpr ⟨fact,member,dependency⟩)⟩
  · exact all_models_slice state _ model

/-- All finite certified observation-only revisions are considered before
inspecting an unresolved producer's children. Descriptor replacement is not
restricted to the stronger descriptor-preserving Refresh contract. -/
inductive View (before : State roles) : State roles → Prop
  | current : View before before
  | refresh : View before middle → GeneralNominalFeedbackSteps.Refresh middle context →
      View before (regenerate middle context)
  | reobserve (revision : GeneralNominalReobservationSteps.Revision middle) :
      View before middle → GeneralNominalReobservationSteps.Certified revision → View before revision.result

theorem view_models (view : View before after) (model : GeneralNominalCommonBridge.Assignment) :
    Models after model ↔ Models before model := by
  induction view with
  | current => exact Iff.rfl
  | refresh _ certificate ih => exact (GeneralNominalCycleSteps.refresh_models certificate model).trans ih
  | reobserve _ _ certificate ih => exact (certificate.exact model).trans ih

/-- A needed head can already be entailed while its source slot is unobserved.
Nested positions are precisely reads of a visible candidate in a certified
observation view; variable patterns do not add reads. -/
inductive Need (registry : Registry) (state : Tracked roles) (focus : Occurrence roles) : Nat → Test → Prop
  | input (index : Fin (roles focus.demand.role).arity) (test : Test) :
      Available state (focus.demand.arguments index).1 test →
      Need registry state focus (focus.demand.arguments index).1 test
  | inspection (observed : State roles) :
      View state.current observed →
      (declaration : Declaration) → declaration ∈ registry.declarations → declaration.role = focus.demand.role →
      (bounds : List (GeneralNominalInspection.Bounds observed.context.state)) →
      GeneralNominalRecursiveCandidates.arguments observed.context focus = some bounds →
      (slot : Fin observed.context.state.base.slots) →
      slot ∈ readsMany observed.context.state
        (GeneralNominalInspection.queries observed.context.state observed.context.interpretation declaration) bounds →
      (test : Test) → Available state (observed.context.state.base.source slot) test →
      Need registry state focus (observed.context.state.base.source slot) test

/-- Waiting paths stop at discharged requests. Historical generation edges
beyond a discharged intermediate cannot introduce a new output dependency. -/
inductive Waiting (state : State roles) (root : Occurrence roles) : Occurrence roles → Prop
  | root : ¬ Discharged state root → Waiting state root root
  | child : Waiting state root parent → (parent,child) ∈ state.edges →
      ¬ Discharged state child → Waiting state root child
  | alias (first last : GeneralNominalDemandMerging.Site roles) :
      Waiting state root first.occurrence → first ∈ state.sites → last ∈ state.sites →
      Alias state first.occurrence.identity last.occurrence.identity →
      ¬ Discharged state last.occurrence → Waiting state root last.occurrence

theorem waiting_generated (path : Waiting state root child) : Generated state root child := by
  induction path with
  | root => exact .root
  | child _ member _ ih => exact .child ih member
  | alias first last _ one two same _ ih => exact .alias ih one two same

theorem waiting_open (path : Waiting state root child) : ¬ Discharged state child := by
  cases path with
  | root unresolved => exact unresolved
  | child _ _ unresolved => exact unresolved
  | alias _ _ _ _ _ _ unresolved => exact unresolved

theorem waiting_trans (first : Waiting state root middle) (last : Waiting state middle child) :
    Waiting state root child := by
  induction last with
  | root => exact first
  | child _ member unresolved ih => exact .child ih member unresolved
  | alias one two _ memberOne memberTwo same unresolved ih => exact .alias one two ih memberOne memberTwo same unresolved

/-- Only the chosen explanation is followed. An unrelated cyclic explanation
cannot invalidate a source or discharged explanation. No installed-packet
premise is imposed on a child whose needed head is being justified. -/
inductive Grounded (registry : Registry) (state : Tracked roles) : Occurrence roles → Prop
  | discharged (producer : Occurrence roles) : Discharged state.current producer → Grounded registry state producer
  | provisional (producer : Occurrence roles)
      (supports : Occurrence roles → Nat → Test → List (Occurrence roles)) :
      (∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
        ∀ identity test, Need registry state child identity test →
          HeadSupported state (supports child identity test) identity test) →
      (∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
        ∀ identity test, Need registry state child identity test →
          ∀ dependency ∈ supports child identity test, Grounded registry state dependency) →
      Grounded registry state producer

def Supported (registry : Registry) (state : Tracked roles) (support : List (Occurrence roles)) : Prop :=
  ∀ producer ∈ support, Grounded registry state producer

def PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) : Prop :=
  GeneralNominalSupportChoices.PacketGuard state packet support ∧ Supported packet.registry state support

def DecisionGuard (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (support : List (Occurrence roles)) : Prop :=
  GeneralNominalSupport.DecisionGuard state registry root support ∧ Supported registry state support

theorem empty_supported (registry : Registry) (state : Tracked roles) : Supported registry state [] := by
  intro _ impossible; cases impossible

theorem source_packet (state : Tracked roles) (packet : Packet roles)
    (guard : GeneralNominalSupportChoices.PacketGuard state packet []) : PacketGuard state packet [] :=
  ⟨guard,empty_supported _ _⟩

theorem source_decision (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (guard : GeneralNominalSupport.DecisionGuard state registry root []) : DecisionGuard registry state root [] :=
  ⟨guard,empty_supported _ _⟩

theorem discharged_supported (registry : Registry) (state : Tracked roles) (support : List (Occurrence roles))
    (done : ∀ producer ∈ support, Discharged state.current producer) : Supported registry state support :=
  fun producer member => .discharged producer (done producer member)

/-- Acyclic provisional explanations remain usable; no child dictionary is
required when the child's available heads already have independent support. -/
theorem provisional_source (registry : Registry) (state : Tracked roles) (producer : Occurrence roles)
    (source : ∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
      ∀ identity test, Need registry state child identity test → HeadSupported state [] identity test) :
    Grounded registry state producer :=
  .provisional producer (fun _ _ _ => []) source (by intro _ _ _ _ _ _ _ impossible; cases impossible)

theorem alias_grounded (registry : Registry) (state : Tracked roles)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites)
    (same : Alias state.current first.occurrence.identity last.occurrence.identity)
    (grounded : Grounded registry state first.occurrence) : Grounded registry state last.occurrence := by
  classical
  by_cases done : Discharged state.current last.occurrence
  · exact .discharged _ done
  have firstOpen : ¬ Discharged state.current first.occurrence :=
    fun resolved => done (.alias first last one two same resolved)
  cases grounded with
  | discharged _ resolved => exact False.elim (firstOpen resolved)
  | provisional _ supports heads dependencies =>
    have path : Waiting state.current first.occurrence last.occurrence :=
      .alias first last (.root firstOpen) one two same done
    exact .provisional _ supports
      (fun child reached => heads child (waiting_trans path reached))
      (fun child reached => dependencies child (waiting_trans path reached))

/-- A closed set of unresolved producers with unavoidable head-support return
edges has no inductive justification. The focus need not belong to this set. -/
theorem trap_excluded (registry : Registry) (state : Tracked roles) (trap : Occurrence roles → Prop)
    (unresolved : ∀ producer, trap producer → ¬ Discharged state.current producer)
    (returns : ∀ producer, trap producer → ∃ child,
      Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
      ∃ identity test, Need registry state child identity test ∧
        ∀ support, HeadSupported state support identity test → ∃ dependency ∈ support, trap dependency)
    (producer : Occurrence roles) (grounded : Grounded registry state producer) : ¬ trap producer := by
  induction grounded with
  | discharged producer done => exact fun member => unresolved producer member done
  | provisional producer supports heads dependencies ih =>
    intro member
    obtain ⟨child,path,openChild,identity,test,needed,back⟩ := returns producer member
    obtain ⟨dependency,included,trapped⟩ := back (supports child identity test)
      (heads child path openChild identity test needed)
    exact ih child path openChild identity test needed dependency included trapped

theorem downstream_blocked (registry : Registry) (state : Tracked roles)
    (identity : Nat) (test : Test) (trap : Occurrence roles → Prop)
    (excluded : ∀ producer, trap producer → ¬ Grounded registry state producer)
    (necessary : ∀ support, HeadSupported state support identity test → ∃ producer ∈ support, trap producer)
    (support : List (Occurrence roles)) (allowed : Supported registry state support) :
    ¬ HeadSupported state support identity test := by
  intro head
  obtain ⟨producer,member,trapped⟩ := necessary support head
  exact excluded producer trapped (allowed producer member)

theorem need_available (needed : Need registry state focus identity test) : Available state identity test := by
  cases needed with
  | input _ _ known => exact known
  | inspection _ _ _ _ _ _ _ _ _ _ known => exact known

theorem empty_ledger_grounded (registry : Registry) (state : Tracked roles) (empty : state.facts = [])
    (producer : Occurrence roles) : Grounded registry state producer := by
  apply provisional_source
  intro child _ _ identity test needed
  have supported := need_available needed
  simpa only [Available,dependencyPool,empty,List.flatMap_nil] using supported

theorem source_conservative_grounded (registry : Registry) (state : Tracked roles)
    (conservative : ∀ model, GeneralNominalState.Models state.source.state model → AllModels state model)
    (producer : Occurrence roles) : Grounded registry state producer := by
  apply provisional_source
  intro child _ _ identity test needed
  obtain ⟨snapshot,observation,head,entailed⟩ := need_available needed
  exact ⟨snapshot,observation,head,fun model valid =>
    entailed model (all_models_slice state _ model (conservative model valid.1))⟩

end Yulang.GeneralNominalDownstreamSupport
