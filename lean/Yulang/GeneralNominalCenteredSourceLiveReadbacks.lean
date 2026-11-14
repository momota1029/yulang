import Yulang.GeneralNominalCenteredInstallObligations

/-! Retain the current finite meanings of initial sources that a live site or
a future candidate can use. Liveness is measured in the leaves of these
presentations, so a justified global replacement can retire an old index. -/
namespace Yulang.GeneralNominalCenteredSourceLiveReadbacks
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredSourceInvariant GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalLabelledOriginClosure
open GeneralNominalScopedRecipeLabels

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

def RelevantOrigin (registry : Registry) (state : State roles) (origin : Origin) : Prop :=
  (∃ site ∈ state.sites, ∃ position, origin = .source (site.center position)) ∨
  ∃ plan : Plan roles, plan.input ∈ state.sites ∧
    GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet ∧ origin ∈ planInputs plan

def FutureRead (registry : Registry) (root : Occurrence roles) (state : State roles) (identity : Nat) : Prop :=
  ∃ after, B4Target.Steps (Step registry root) state after ∧
    ∃ origin, RelevantOrigin registry after origin ∧ (∃ model, Models after model) ∧
      ∀ model, Models after model → Same model origin (.source identity)

theorem FutureRead.before {before after : State roles} (step : Step registry root before after)
    (read : FutureRead registry root after identity) : FutureRead registry root before identity := by
  obtain ⟨last,path,origin,relevant,inhabited,same⟩ := read
  have joined : B4Target.Steps (Step registry root) before last := by
    clear relevant inhabited same
    induction path with
    | refl => exact .tail .refl step
    | tail path next ih => exact .tail ih next
  exact ⟨last,joined,origin,relevant,inhabited,same⟩

theorem FutureRead.site (site : Site roles) (member : site ∈ state.sites) (position)
    (inhabited : ∃ model, Models state model) : FutureRead registry root state (site.center position) :=
  ⟨state,.refl,.source (site.center position),Or.inl ⟨site,member,position,rfl⟩,inhabited,
    fun model _ => source_self model _⟩

theorem FutureRead.candidate (plan : Plan roles) (registered : plan.input ∈ state.sites)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (member : Origin.source identity ∈ planInputs plan)
    (inhabited : ∃ model, Models state model) : FutureRead registry root state identity :=
  ⟨state,.refl,.source identity,Or.inr ⟨plan,registered,enabled,member⟩,inhabited,
    fun model _ => source_self model _⟩

structure Retention (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (state : State roles) (remaining : List Nat)
    (facts : List (GeneralNominalCenteredSupport.Fact roles)) where
  value : ∀ identity, identity ∈ GeneralNominalState.sources context.state →
    FutureRead registry root state identity →
    Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts)
      context (origins context) remaining (keyMenu registry) (.source identity)
  vocabulary : ∀ identity member read, Vocabulary (testMenu context registry) (value identity member read).term

def Retention.Live (retained : Retention registry context root state remaining facts) (hole : Nat) : Prop :=
  ∃ identity member read, hole ∈ (retained.value identity member read).term.leaves

theorem Retention.live_mem (retained : Retention registry context root state remaining facts)
    (live : retained.Live hole) : hole ∈ remaining := by
  obtain ⟨identity,member,read,present⟩ := live
  exact (retained.value identity member read).labelled.2.2 hole present

theorem Retention.opaque_mem (retained : Retention registry context root state remaining facts)
    (member : identity ∈ GeneralNominalState.sources context.state)
    (read : FutureRead registry root state identity)
    (leaf : (retained.value identity member read).term = .leaf hole) : hole ∈ remaining := by
  apply retained.live_mem
  exact ⟨identity,member,read,by rw [leaf]; exact List.mem_singleton_self _⟩

structure Coverage' (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (state : State roles) (inventory : Inventory)
    (journal : Journal context root state.erased inventory)
    extends Coverage registry context root state inventory journal where
  retention : Retention registry context root state inventory.holes toCoverage.centeredFacts

def Retention.initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (holes : remaining = GeneralNominalIndexedHoleReadback.holes (GeneralNominalSourceFrontier.frontier context.state)) :
    Retention registry context root (initial context root) remaining facts where
  value := fun identity member _ => holes ▸ frontier_value (GeneralNominalSourceFrontier.source_member member)
  vocabulary := by intro identity member read; cases holes; trivial

def Retention.full (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (state : State roles)
    (holes : remaining = GeneralNominalIndexedHoleReadback.holes (GeneralNominalSourceFrontier.frontier context.state)) :
    Retention registry context root state remaining facts where
  value := fun identity member _ => holes ▸ frontier_value (GeneralNominalSourceFrontier.source_member member)
  vocabulary := by intro identity member read; cases holes; trivial

theorem initialized
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root) :
    ∃ inventory : Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory ∧
      ∃ journal : Journal context root (initial context root).erased inventory,
        Nonempty (Coverage' registry context root (initial context root) inventory journal) := by
  obtain ⟨inventory,holes,valid,journal,⟨coverage⟩⟩ := GeneralNominalCenteredSourceInvariant.initialized source point
  exact ⟨inventory,holes,valid,journal,⟨coverage,Retention.initial context root holes⟩⟩

def Retention.step (retained : Retention registry context root before remaining facts)
    (step : Step registry root before after) : Retention registry context root after remaining facts where
  value := fun identity member read => (retained.value identity member (read.before step)).restrict (by
    intro model valid
    rw [GeneralNominalCenteredTrustedTransport.models_step step] at valid
    exact valid)
  vocabulary := fun identity member read => retained.vocabulary identity member (read.before step)

def Retention.strengthen (retained : Retention registry context root state remaining first)
    (included : first ⊆ last) : Retention registry context root state remaining last where
  value := fun identity member read => (retained.value identity member read).restrict (by
    intro model valid
    exact ⟨valid.1,valid.2.1,fun fact present => valid.2.2 fact (included present)⟩)
  vocabulary := retained.vocabulary

def Retention.replace (retained : Retention registry context root state remaining facts)
    (replacement : Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts)
      context (origins context) (remaining.erase hole) (keyMenu registry) (origins context hole))
    (vocabulary : Vocabulary (testMenu context registry) replacement.term) :
    Retention registry context root state (remaining.erase hole) facts where
  value := fun identity member read =>
    GeneralNominalLabelledExposureElimination.Value.replace (retained.value identity member read) replacement
  vocabulary := fun identity member read =>
    GeneralNominalCaptureRefinement.replacement_vocabulary (retained.vocabulary identity member read) vocabulary

theorem Retention.eliminated_not_live (retained : Retention registry context root state remaining facts)
    (replacement : Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts)
      context (origins context) (remaining.erase hole) (keyMenu registry) (origins context hole))
    (vocabulary : Vocabulary (testMenu context registry) replacement.term)
    (distinct : remaining.Nodup) : ¬ (retained.replace replacement vocabulary).Live hole :=
  fun live => distinct.not_mem_erase ((retained.replace replacement vocabulary).live_mem live)

end Yulang.GeneralNominalCenteredSourceLiveReadbacks
