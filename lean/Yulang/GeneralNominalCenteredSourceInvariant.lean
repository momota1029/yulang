import Yulang.GeneralNominalCenteredTrustedTransport
import Yulang.GeneralNominalCenteredSiteLabels

/-! A concrete source invariant over the current surviving holes. Registered
centers share the journal's source patterns. Selected trusted explanations
retain their own coarse predicates, including earlier output-binder values. -/
namespace Yulang.GeneralNominalCenteredSourceInvariant
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalIdentityJournal

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

def origins (context : GeneralNominalCandidates.Context) : Nat → Origin :=
  GeneralNominalIndexedHoleReadback.origin (GeneralNominalSourceFrontier.frontier context.state)

def sourceMenu (declaration : Declaration) : List Pattern :=
  declaration.head ++ GeneralNominalSchemaBudget.menu declaration

def sourcePatterns (registry : Registry) : List Pattern :=
  registry.declarations.flatMap fun declaration => (sourceMenu declaration).map normalize

def keyMenu (registry : Registry) : List Nat :=
  GeneralNominalSourceLabelVocabulary.collectArgs (sourcePatterns registry)

def testMenu (context : GeneralNominalCandidates.Context) (registry : Registry) : List Test :=
  registry.declarations.flatMap fun declaration => (sourceMenu declaration).flatMap fun pattern =>
    GeneralNominalSchemaVocabulary.vocabulary
      (GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize pattern))

theorem source_scoped (visible : declaration ∈ registry.declarations)
    (member : pattern ∈ sourceMenu declaration) :
    GeneralNominalSourceLabelVocabulary.Scoped (keyMenu registry) (normalize pattern) :=
  GeneralNominalSourceLabelVocabulary.collect_args_scoped _ _
    (List.mem_flatMap.mpr ⟨declaration,visible,List.mem_map.mpr ⟨pattern,member,rfl⟩⟩)

theorem templates (context : GeneralNominalCandidates.Context) (registry : Registry) :
    NodeTemplates context (keyMenu registry) (testMenu context registry) := by
  intro test member canonical
  obtain ⟨declaration,visible,member⟩ := List.mem_flatMap.mp member
  obtain ⟨pattern,present,member⟩ := List.mem_flatMap.mp member
  exact GeneralNominalRequestTemplates.source_templates context _ (source_scoped visible present) test member canonical

theorem output_test (member : test ∈ GeneralNominalSchemaVocabulary.registryVocabulary context registry) :
    test ∈ testMenu context registry := by
  obtain ⟨declaration,visible,member⟩ := List.mem_flatMap.mp member
  obtain ⟨pattern,present,member⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨declaration,visible,List.mem_flatMap.mpr
    ⟨pattern,List.mem_append_right _ present,member⟩⟩

def SiteValues (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (remaining keys : List Nat) (tests : List Test)
    (labels : Occurrence roles → List Pattern) (site : Site roles) : Prop :=
  ∃ values : (position : Fin (roles site.occurrence.demand.role).arity) →
      Value models context (origins context) remaining keys (.source (site.center position)),
    labels site.occurrence = List.ofFn (fun position => (values position).pattern) ∧
      ∀ position, Vocabulary tests (values position).term

def OriginValues (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (remaining keys : List Nat) (tests : List Test)
    (relevant : List Origin) : Prop :=
  ∀ origin ∈ relevant, ∃ value : Value models context (origins context) remaining keys origin,
    Vocabulary tests value.term

def siteOrigins (site : Site roles) : List Origin := List.ofFn fun position => .source (site.center position)

def planInputs (plan : Plan roles) : List Origin :=
  siteOrigins plan.input ++ plan.headSchema.variables.map (fun entry => entry.origin) ++
    plan.packet.declaration.inputNames.map (fun name => .source (plan.binder name))

def inputOrigins (facts : List (GeneralNominalCenteredSupport.Fact roles)) : List Origin :=
  facts.flatMap fun fact => match fact with
    | .input plan | .output plan => planInputs plan
    | .legacy fact => GeneralNominalSharedSupport.inputOrigins [fact]
    | .merge first last => siteOrigins first ++ siteOrigins last

def binderOrigins (facts : List (GeneralNominalCenteredSupport.Fact roles)) : List Origin :=
  facts.flatMap fun fact => match fact with
    | .output plan => (GeneralNominalPacketSupport.namedSchema plan.packet).variables.filterMap fun entry =>
        if entry.mode = .actual ∧ entry.name ∈ plan.packet.declaration.outputNames
        then some (.source (plan.binder entry.name)) else none
    | _ => []

theorem site_restrict (known : SiteValues before context remaining keys tests labels site)
    (included : ∀ model, after model → before model) : SiteValues after context remaining keys tests labels site := by
  obtain ⟨values,same,vocabulary⟩ := known
  exact ⟨fun position => (values position).restrict included,same,vocabulary⟩

theorem origins_restrict (known : OriginValues before context remaining keys tests relevant)
    (included : ∀ model, after model → before model) : OriginValues after context remaining keys tests relevant := by
  intro origin member
  obtain ⟨value,vocabulary⟩ := known origin member
  exact ⟨value.restrict included,vocabulary⟩

structure Coverage (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (state : State roles) (inventory : Inventory)
    (journal : Journal context root state.erased inventory) where
  identity : IdentityLabels journal.labels
  rawFacts : List (GeneralNominalSupport.Fact roles)
  rawReadbacks : GeneralNominalSharedSupport.Readbacks
  rawTrusted : GeneralNominalSharedSupport.Trusted state.erased rawFacts rawReadbacks
  rawInputs : GeneralNominalSourceProducerHandoff.TrustedInputs state.erased rawFacts context
    (origins context) inventory.holes (keyMenu registry) (testMenu context registry)
  centeredFacts : List (GeneralNominalCenteredSupport.Fact roles)
  centeredTrusted : GeneralNominalCenteredSupport.Trusted state.erased state.sourceSites state.plans centeredFacts
  legacyIncluded : ∀ fact ∈ rawFacts, .legacy fact ∈ centeredFacts
  sites : ∀ site ∈ state.sites, SiteValues
    (GeneralNominalCenteredSupport.Models state.erased state.sourceSites centeredFacts)
    context inventory.holes (keyMenu registry) (testMenu context registry) journal.labels site
  inputs : OriginValues (GeneralNominalCenteredSupport.Models state.erased state.sourceSites centeredFacts)
    context inventory.holes (keyMenu registry) (testMenu context registry) (inputOrigins centeredFacts)
  binders : OriginValues (GeneralNominalCenteredSupport.Models state.erased state.sourceSites centeredFacts)
    context inventory.holes (keyMenu registry) (testMenu context registry) (binderOrigins centeredFacts)

theorem trusted_inputs (coverage : Coverage registry context root state inventory journal) :
    GeneralNominalSourceProducerHandoff.TrustedInputs state.erased coverage.rawFacts context
      (origins context) inventory.holes (keyMenu registry) (testMenu context registry) := coverage.rawInputs

theorem registered_site (path : B4Target.Steps (Step registry root) (initial context root) state)
    (coverage : Coverage registry context root state inventory journal) (member : site ∈ state.sites) :
    SiteValues (Models state) context inventory.holes (keyMenu registry) (testMenu context registry) journal.labels site :=
  site_restrict (coverage.sites site member)
    (fun _ valid => GeneralNominalCenteredSourceTrace.trusted_models path coverage.centeredTrusted valid)

theorem promoted_output (path : B4Target.Steps (Step registry root) (initial context root) state)
    (coverage : Coverage registry context root state inventory journal)
    (present : GeneralNominalSupport.Fact.outputs packet support ∈ coverage.rawFacts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ value : Value (GeneralNominalSharedSupport.Models state.erased coverage.rawFacts) context
      (origins context) inventory.holes (keyMenu registry) (.source output.target),
      Vocabulary (testMenu context registry) value.term := by
  apply GeneralNominalSettledLabelledLedger.promoted_labelled coverage.rawTrusted ?_
    (templates := templates context registry) coverage.rawInputs present output member
  intro packet support present entry used
  have recorded := GeneralNominalSettledSupport.trusted_members
    (GeneralNominalSharedSupport.trusted_old coverage.rawTrusted) _ present
  obtain ⟨visible,constructors,interpretation⟩ :=
    GeneralNominalCenteredTrustedTransport.output_configuration path packet support recorded
  exact ⟨GeneralNominalRegistrySourceTemplates.packet_canonical packet entry used,
    output_test (GeneralNominalSchemaVocabulary.packet_vocabulary context packet visible constructors interpretation
      (List.mem_map.mpr ⟨entry,used,rfl⟩))⟩

theorem output_binder (coverage : Coverage registry context root state inventory journal)
    (present : GeneralNominalCenteredSupport.Fact.output plan ∈ coverage.centeredFacts)
    (entry : GeneralNominalMaterialization.Use)
    (used : entry ∈ (GeneralNominalPacketSupport.namedSchema plan.packet).variables)
    (actual : entry.mode = .actual) (member : entry.name ∈ plan.packet.declaration.outputNames) :
    GeneralNominalSettledSupport.PacketSettled state.erased.current plan.packet ∧
      ∃ value : Value (GeneralNominalCenteredSupport.Models state.erased state.sourceSites coverage.centeredFacts)
        context (origins context) inventory.holes (keyMenu registry) (.source (plan.binder entry.name)),
        Vocabulary (testMenu context registry) value.term :=
  ⟨GeneralNominalCenteredSupport.outputs_settled coverage.centeredTrusted present,
    coverage.binders _ (List.mem_flatMap.mpr ⟨.output plan,present,List.mem_filterMap.mpr
      ⟨entry,used,ite_eq_left ⟨actual,member⟩⟩⟩)⟩

theorem initial_site
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ position, (root.demand.arguments position).1 = (root.demand.arguments position).2)
    (same : labels root = GeneralNominalSourceInitialization.rootPatterns context root) :
    SiteValues models context
      (GeneralNominalIndexedHoleReadback.holes (GeneralNominalSourceFrontier.frontier context.state))
      (keyMenu registry) (testMenu context registry) labels (rootSite context.state.seed root) := by
  let values : (position : Fin (roles root.demand.role).arity) →
      Value models context (origins context)
        (GeneralNominalIndexedHoleReadback.holes (GeneralNominalSourceFrontier.frontier context.state))
        (keyMenu registry) (.source ((rootSite context.state.seed root).center position)) := fun position =>
    (GeneralNominalLabelledOriginClosure.initial_value (models := models) (keys := keyMenu registry) source position).alias
      (fun model _ => by
        rw [point_center context.state.seed root position (point position)]
        exact source_self model _)
  exact ⟨values,same,fun _ => trivial⟩

theorem initial_coverage
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ position, (root.demand.arguments position).1 = (root.demand.arguments position).2)
    (journal : Journal context root (initial context root).erased inventory)
    (holes : inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length)
    (identity : IdentityLabels journal.labels)
    (same : journal.labels root = GeneralNominalSourceInitialization.rootPatterns context root) :
    Nonempty (Coverage registry context root (initial context root) inventory journal) := by
  refine ⟨{
    identity := identity
    rawFacts := []
    rawReadbacks := []
    rawTrusted := .source
    rawInputs := by intro origin member; cases member
    centeredFacts := []
    centeredTrusted := .source
    legacyIncluded := by intro fact member; cases member
    sites := ?_
    inputs := by intro origin member; cases member
    binders := by intro origin member; cases member }⟩
  intro site member
  cases List.mem_singleton.mp member
  rw [holes]
  exact initial_site source point same

theorem initialized
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : GeneralNominalActualBudget.PointSource context root) :
    ∃ inventory : Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory ∧
      ∃ journal : Journal context root (initial context root).erased inventory,
        Nonempty (Coverage registry context root (initial context root) inventory journal) := by
  obtain ⟨inventory,holes,valid,journal,identity,same⟩ :=
    GeneralNominalCenteredIdentityJournal.initial_journal source (keyMenu registry)
  exact ⟨inventory,holes,valid,journal,initial_coverage source point.rootInputs journal holes identity same⟩

def Coverage.transport (coverage : Coverage registry context root before inventory journal)
    (step : Step registry root before after) (sites : after.sites ⊆ before.sites)
    (next : Journal context root after.erased inventory) (same : next.labels = journal.labels) :
    Coverage registry context root after inventory next where
  identity := same ▸ coverage.identity
  rawFacts := coverage.rawFacts
  rawReadbacks := coverage.rawReadbacks
  rawTrusted := GeneralNominalCenteredSourcePersistence.trusted_step step coverage.rawTrusted
  rawInputs := GeneralNominalCenteredSourcePersistence.trusted_inputs_step step coverage.rawInputs
  centeredFacts := coverage.centeredFacts
  centeredTrusted := GeneralNominalCenteredTrustedTransport.trusted_step step coverage.centeredTrusted
  legacyIncluded := coverage.legacyIncluded
  sites := by
    intro site member
    rw [same]
    apply site_restrict (coverage.sites site (sites member))
    intro model valid
    rw [GeneralNominalCenteredTrustedTransport.models_step step] at valid
    exact valid
  inputs := origins_restrict coverage.inputs (by
    intro model valid
    rw [GeneralNominalCenteredTrustedTransport.models_step step] at valid
    exact valid)
  binders := origins_restrict coverage.binders (by
    intro model valid
    rw [GeneralNominalCenteredTrustedTransport.models_step step] at valid
    exact valid)

end Yulang.GeneralNominalCenteredSourceInvariant
