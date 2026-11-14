import Yulang.GeneralNominalCenteredSourceLiveProduction

/-! Exact snapshot support is a semantic requirement on the selected ledger.
It asks only for cached observations, rather than every installed output.
The stronger syntactic candidate is stated separately to expose settlement. -/
namespace Yulang.GeneralNominalCenteredSourceSnapshotLedger
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredSourceInvariant GeneralNominalCenteredSourceLiveReadbacks
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalCenteredInstallObligations

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

def LedgerComplete (state : State roles) (facts : List (GeneralNominalCenteredSupport.Fact roles)) : Prop :=
  (∀ plan ∈ state.plans, GeneralNominalCenteredSupport.Fact.input plan ∈ facts ∧
    GeneralNominalCenteredSupport.Fact.output plan ∈ facts) ∧
  ∀ first last support, GeneralNominalSupport.Fact.merge first last support ∈ state.erased.facts →
    GeneralNominalCenteredSupport.Fact.legacy (.merge first last support) ∈ facts

theorem LedgerComplete.initial : LedgerComplete (initial context root) [] := by
  constructor
  · intro plan member; cases member
  · intro first last support recorded; cases recorded

theorem LedgerComplete.settled (complete : LedgerComplete state facts)
    (trusted : GeneralNominalCenteredSupport.Trusted state.erased state.sourceSites state.plans facts)
    (member : plan ∈ state.plans) :
    GeneralNominalSettledSupport.PacketSettled state.erased.current plan.packet :=
  GeneralNominalCenteredSupport.outputs_settled trusted (complete.1 plan member).2

def SnapshotReadbacks (state : State roles) (facts : List (GeneralNominalCenteredSupport.Fact roles)) : Prop :=
  ∀ identity test observation,
    GeneralNominalSupport.Head state.erased.current.context.state identity test observation →
    ∀ model, GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts model →
      observation.Holds model

theorem SnapshotReadbacks.initial : SnapshotReadbacks (initial context root) facts := by
  intro identity test observation seen model valid
  exact GeneralCanonicalObservations.recorded_sound context.state model valid.1
    (GeneralNominalSupport.head_recorded seen)

theorem SnapshotReadbacks.strengthen (sound : SnapshotReadbacks state first) (included : first ⊆ last) :
    SnapshotReadbacks state last := by
  intro identity test observation seen model valid
  exact sound identity test observation seen model
    ⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (included member)⟩

theorem SnapshotReadbacks.readback (sound : SnapshotReadbacks state facts)
    (same : plan.packet.context = state.erased.current.context) :
    GeneralNominalCenteredSupport.Readback state.erased state.sourceSites facts plan := by
  intro slot visited test observation seen model valid
  exact sound (plan.packet.context.state.base.source slot) test observation
    (by simpa only [same] using seen) model valid

structure Coverage'' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (state : State roles) (inventory : Inventory)
    (journal : Journal context root state.erased inventory)
    extends Coverage' registry context root state inventory journal where
  snapshot : SnapshotReadbacks state toCoverage'.centeredFacts

theorem initialized
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root) :
    ∃ inventory : Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory ∧
      ∃ journal : Journal context root (initial context root).erased inventory,
        Nonempty (Coverage'' registry context root (initial context root) inventory journal) := by
  obtain ⟨inventory,holes,valid,journal,⟨coverage⟩⟩ :=
    GeneralNominalCenteredSourceLiveReadbacks.initialized source point
  exact ⟨inventory,holes,valid,journal,⟨coverage,SnapshotReadbacks.initial⟩⟩

def InputReadbackAndOrigins'' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root,
    Retention registry context root job.state job.inventory.holes job.coverage.centeredFacts →
    SnapshotReadbacks job.state job.coverage.centeredFacts →
    GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites job.coverage.centeredFacts job.plan ∧
    OriginValues
      (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites (.input job.plan :: job.coverage.centeredFacts))
      context job.inventory.holes (keyMenu registry) (testMenu context registry) (planInputs job.plan)

theorem input_readback (job : Installation registry context root)
    (sound : SnapshotReadbacks job.state job.coverage.centeredFacts) :
    GeneralNominalCenteredSupport.Readback job.state.erased job.state.sourceSites job.coverage.centeredFacts job.plan :=
  sound.readback job.enabled.1.2.1

theorem trusted_input (job : Installation registry context root)
    (sound : SnapshotReadbacks job.state job.coverage.centeredFacts) :
    GeneralNominalCenteredSupport.Trusted job.after.erased job.after.sourceSites job.after.plans
      (.input job.plan :: job.coverage.centeredFacts) := by
  obtain ⟨support,recorded⟩ := GeneralNominalCenteredOriginFrameProduction.input_recorded job
  refine .input job.plan support
    (GeneralNominalCenteredTrustedTransport.trusted_step job.step job.coverage.centeredTrusted)
    (List.mem_cons_self ..) recorded ?_
  intro slot visited test observation seen model valid
  apply input_readback job sound slot visited test observation seen model
  rw [GeneralNominalCenteredTrustedTransport.models_step job.step] at valid
  exact valid

/-- Exact readback only at actual novel guarded nonterminal installations,
with a separately chosen trusted ledger for each. -/
def ExecutableReadbacks (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∀ plan : Plan roles, ∀ support,
    GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence →
    GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
    ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet →
    PacketGuard state plan support → plan.packet.declaration.requirements ≠ [] →
    ∃ facts, GeneralNominalCenteredSupport.Trusted state.erased state.sourceSites state.plans facts ∧
      GeneralNominalCenteredSupport.Readback state.erased state.sourceSites facts plan

theorem Coverage''.executable (coverage : Coverage'' registry context root state inventory journal) :
    ExecutableReadbacks registry root state := by
  intro plan support generated enabled novel guard children
  exact ⟨coverage.centeredFacts,coverage.centeredTrusted,coverage.snapshot.readback enabled.1.2.1⟩

end Yulang.GeneralNominalCenteredSourceSnapshotLedger

