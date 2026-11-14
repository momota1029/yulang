import Yulang.GeneralNominalCenteredSourceConstruction
import Yulang.GeneralNominalCenteredChildSourceValues
import Yulang.GeneralNominalCenteredCoverageReplacement

/-! Three source obligations for a nonterminal centered installation. The
origin stage supplies coarse trusted readbacks; exposure completes individual
head matching; reconciliation supplies one common historical presentation. -/
namespace Yulang.GeneralNominalCenteredInstallObligations
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalCenteredSourceInvariant GeneralNominalIdentityJournal
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalOpenPatternLabels
open GeneralNominalCaptureRefinement (Operation)

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

structure Installation (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) where
  state : State roles
  reachable : B4Target.Steps (Step registry root) (initial context root) state
  inventory : Inventory
  valid : Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory
  journal : Journal context root state.erased inventory
  coverage : Coverage registry context root state inventory journal
  plan : Plan roles
  support : List (Occurrence roles)
  generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence
  enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet
  novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet
  guard : PacketGuard state plan support
  children : plan.packet.declaration.requirements ≠ []

noncomputable def Installation.after (job : Installation registry context root) : State roles :=
  install job.state job.plan job.support

theorem Installation.step (job : Installation registry context root) :
    Step registry root job.state job.after :=
  ⟨job.plan.packet.site.occurrence,job.generated,.install job.plan job.support job.enabled job.novel job.guard⟩

/-- Old sites retain their journal forests. Newly selected input/output facts
have values under this very ledger, including all actual output-binder uses.
New child forests are constructed only after captures have been reconciled. -/
structure OriginFrame (job : Installation registry context root) (inventory : Inventory)
    (journal : Journal context root job.state.erased inventory) where
  identity : IdentityLabels journal.labels
  rawFacts : List (GeneralNominalSupport.Fact roles)
  rawReadbacks : GeneralNominalSharedSupport.Readbacks
  rawTrusted : GeneralNominalSharedSupport.Trusted job.after.erased rawFacts rawReadbacks
  rawInputs : GeneralNominalSourceProducerHandoff.TrustedInputs job.after.erased rawFacts context
    (origins context) inventory.holes (keyMenu registry) (testMenu context registry)
  facts : List (GeneralNominalCenteredSupport.Fact roles)
  trusted : GeneralNominalCenteredSupport.Trusted job.after.erased job.after.sourceSites job.after.plans facts
  legacyIncluded : ∀ fact ∈ rawFacts, .legacy fact ∈ facts
  selected : GeneralNominalCenteredSupport.Fact.input job.plan ∈ facts
  sites : ∀ site ∈ job.state.sites, SiteValues
    (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites facts)
    context inventory.holes (keyMenu registry) (testMenu context registry) journal.labels site
  inputs : OriginValues (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites facts)
    context inventory.holes (keyMenu registry) (testMenu context registry) (inputOrigins facts)
  binders : OriginValues (GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites facts)
    context inventory.holes (keyMenu registry) (testMenu context registry) (binderOrigins facts)

variable {job : Installation registry context root} {inventory : Inventory}
variable {journal : Journal context root job.state.erased inventory}

def OriginFrame.models (frame : OriginFrame job inventory journal) : GeneralNominalCommonBridge.Assignment → Prop :=
  GeneralNominalCenteredSupport.Models job.after.erased job.after.sourceSites frame.facts

def CapturePart (frame : OriginFrame job inventory journal) (name : Nat) (term : Expr Nat) : Prop :=
  ∃ value : Value frame.models context (origins context) inventory.holes (keyMenu registry)
    (.source (job.plan.binder name)), value.term = term ∧ Vocabulary (testMenu context registry) term

def IndividualHeadMatching (frame : OriginFrame job inventory journal) : Prop :=
  GeneralNominalMatchedAssembly.Aligned
    (fun pattern label => ∃ term, Label context label term ∧
      GeneralNominalHeadMatchMass.Matches (CapturePart frame)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
    (normalizeArgs job.plan.packet.declaration.head) (journal.labels job.plan.packet.site.occurrence)

/-- The list records genuine elimination of original holes. Positive depth
increments allow its trace to be prepended to an arbitrary later trace. The
semantic obligations are carried by the origin frame at the resulting end. -/
inductive Changes (context : GeneralNominalCandidates.Context) (keys : List Nat) :
    Inventory → Inventory → List Operation → Prop
  | refl (inventory : Inventory) : Changes context keys inventory inventory []
  | next (op : Operation)
      (present : op.hole ∈ before.holes)
      (label : Label context op.pattern op.tree)
      (bounded : GeneralNominalSharedEnumeration.Bounded (before.holes.erase op.hole)
        (GeneralNominalSourceLabelVocabulary.tests keys) op.extra (GeneralNominalPatternInventory.encode op.pattern))
      (positive : 0 < op.extra)
      (rest : Changes context keys (op.updated before) after operations) :
      Changes context keys before after (op :: operations)

theorem Changes.prepend (changes : Changes context keys before middle operations)
    (tail : Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth middle after count) :
    ∃ combined, Trace (GeneralNominalSourceLabelVocabulary.tests keys) combined before after
      (count + operations.length) := by
  induction changes with
  | refl => exact ⟨growth,tail⟩
  | next op present label bounded positive rest ih =>
    obtain ⟨later,trace⟩ := ih tail
    obtain ⟨combined,trace⟩ := GeneralNominalCaptureRefinement.prepend_trace present bounded positive trace
    exact ⟨combined,by simpa only [List.length_cons,Nat.add_assoc] using trace⟩

theorem Changes.trace (changes : Changes context keys before after operations) :
    ∃ growth, Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth before after operations.length := by
  simpa only [Nat.zero_add] using changes.prepend (Trace.refl (growth := fun _ => 0) after)

theorem Changes.transport_journal (changes : Changes context keys before after operations)
    (journal : Journal context root state before) :
    ∃ next : Journal context root state after,
      next.labels = GeneralNominalCaptureFamilies.transformLabels operations journal.labels := by
  induction changes with
  | refl => exact ⟨journal,rfl⟩
  | next op present label bounded positive rest ih => exact ih (journal.replace label op.hole op.extra)

def NewlyRelevantOrigins (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root, Nonempty (OriginFrame job job.inventory job.journal)

def FullReportExposures (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root, ∀ _frame : OriginFrame job job.inventory job.journal,
    ∃ updated operations, Changes context (keyMenu registry) job.inventory updated operations ∧
      ∃ journal : Journal context root job.state.erased updated,
        journal.labels = GeneralNominalCaptureFamilies.transformLabels operations job.journal.labels ∧
        ∃ refined : OriginFrame job updated journal, IndividualHeadMatching refined

/-- One common presentation, interpreted at the stored binder centers, with
every old site and historical packet retaining its forest. -/
structure CommonCaptures (frame : OriginFrame job inventory journal) where
  labels : Occurrence roles → List Pattern
  identity : IdentityLabels labels
  rootSame : labels root = journal.labels root
  oldSites : ∀ site ∈ job.state.sites, labels site.occurrence = journal.labels site.occurrence
  history : ∀ prior ∈ job.state.erased.current.packets, prior.declaration.requirements ≠ [] →
    GeneralNominalCompatibleJournalExtension.Agrees journal.labels labels prior
  presentation : GeneralNominalCanonicalPacketTransport.Presentation context labels job.plan.packet
  scopes : ∀ name, GeneralNominalSourceLabelVocabulary.Scoped (keyMenu registry) (presentation.capture name)
  represented : ∀ name, GeneralNominalSharedCaptures.Needed job.plan.packet name →
    GeneralNominalIndexedHoleReadback.Readback frame.models (origins context) inventory.holes
      (.source (job.plan.binder name)) (presentation.trees name) ∧
    GeneralPatternVariableProvenance.Uses (fun hole => hole ∈ inventory.holes) (presentation.capture name) ∧
    Vocabulary (testMenu context registry) (presentation.trees name)

theorem CommonCaptures.finish (frame : OriginFrame job inventory journal)
    (common : CommonCaptures frame) :
    ∃ next : Journal context root job.after.erased inventory,
      Nonempty (Coverage registry context root job.after inventory next) := by
  obtain ⟨next,equal⟩ := GeneralNominalCompatibleJournalExtension.install_extension journal common.labels
    common.rootSame common.history job.plan.packet job.support (fun _ => ⟨common.presentation⟩)
  have constructors : job.plan.packet.context.state.constructors = context.state.constructors := by
    rw [job.enabled.1.2.1]
    exact (GeneralNominalCenteredSourceTrace.configuration_trace job.reachable).2.1
  have interpretation : job.plan.packet.context.interpretation = context.interpretation := by
    rw [job.enabled.1.2.1]
    exact (GeneralNominalCenteredSourceTrace.configuration_trace job.reachable).2.2
  refine ⟨next,⟨{
    identity := equal ▸ common.identity
    rawFacts := frame.rawFacts
    rawReadbacks := frame.rawReadbacks
    rawTrusted := frame.rawTrusted
    rawInputs := frame.rawInputs
    centeredFacts := frame.facts
    centeredTrusted := frame.trusted
    legacyIncluded := frame.legacyIncluded
    sites := ?_
    inputs := frame.inputs
    binders := frame.binders }⟩⟩
  intro site member
  change site ∈ job.state.sites ++ job.plan.emitted at member
  rcases List.mem_append.mp member with old | child
  · obtain ⟨values,same,vocab⟩ := frame.sites site old
    exact ⟨values,(congrFun equal site.occurrence).trans ((common.oldSites site old).trans same),vocab⟩
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp child
    exact GeneralNominalCenteredChildSourceValues.child_site job.state.erased.current job.enabled
      constructors interpretation (fun _ valid => valid.2.2 (.input job.plan) frame.selected)
      common.presentation.capture common.presentation.trees common.presentation.captureLabels common.scopes
      common.represented clause.val clause.property
      (job.plan.packet.checked.signature.2.2.2 clause.val clause.property) next.labels
      ((congrFun equal _).trans (common.presentation.children clause.val clause.property _))

def CaptureReconciliation (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ job : Installation registry context root, ∀ inventory,
    Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory →
    ∀ journal : Journal context root job.state.erased inventory,
    ∀ frame : OriginFrame job inventory journal, IndividualHeadMatching frame →
      ∃ updated operations,
        Changes context (keyMenu registry) inventory updated operations ∧
        ∃ next : Journal context root job.state.erased updated,
          next.labels = GeneralNominalCaptureFamilies.transformLabels operations journal.labels ∧
          ∃ refined : OriginFrame job updated next, Nonempty (CommonCaptures refined)

theorem nonterminal_install_of_three
    (origins : NewlyRelevantOrigins registry context root)
    (exposures : FullReportExposures registry context root)
    (captures : CaptureReconciliation registry context root) :
    GeneralNominalCenteredSourceConstruction.NonterminalInstallPreservation registry context root := by
  intro state reachable inventory valid journal coverage plan support generated enabled novel guard children
  let job : Installation registry context root :=
    ⟨state,reachable,inventory,valid,journal,coverage,plan,support,generated,enabled,novel,guard,children⟩
  obtain ⟨frame⟩ := origins job
  obtain ⟨middle,operations,changes,middleJournal,_,refined,matched⟩ := exposures job frame
  obtain ⟨firstGrowth,trace⟩ := changes.trace
  obtain ⟨updated,lastOperations,lastChanges,next,_,finalFrame,⟨common⟩⟩ :=
    captures job middle (trace_valid trace valid) middleJournal refined matched
  obtain ⟨growth,tail⟩ := lastChanges.trace
  obtain ⟨afterJournal,coverageAfter⟩ := common.finish finalFrame
  obtain ⟨combined,all⟩ := changes.prepend tail
  exact ⟨updated,combined,_,all,afterJournal,coverageAfter⟩

theorem simulation_of_three
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root)
    (origins : NewlyRelevantOrigins registry context root)
    (exposures : FullReportExposures registry context root)
    (captures : CaptureReconciliation registry context root) :
    Nonempty (GeneralNominalCenteredJournalSimulation.Simulation registry context root) :=
  GeneralNominalCenteredSourceConstruction.simulation source point
    (nonterminal_install_of_three origins exposures captures)

end Yulang.GeneralNominalCenteredInstallObligations
