import Yulang.GeneralNominalCenteredOriginSeparation

/-! The current coverage type only requires surviving holes for registered
root centers at initialization. This characterizes its inventory quantifier;
it does not assert that an arbitrary such inventory arose by refinement. -/
namespace Yulang.GeneralNominalCenteredInitialInventories
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredSourceInvariant
open GeneralNominalCanonicalHoleJournal GeneralNominalHoleElimination
open GeneralNominalLabelledOriginClosure GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalSourceInitialization GeneralNominalIndexedHoleReadback
open GeneralNominalSourceLabelVocabulary GeneralNominalScopedRecipeLabels

variable {roles : Roles.RoleDecls} {root : Occurrence roles}
variable {registry : Registry} {context : GeneralNominalCandidates.Context}

def root_value
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (position : Fin (roles root.demand.role).arity)
    (retained : index (GeneralNominalSourceFrontier.frontier context.state)
      (root.demand.arguments position).1 ∈ remaining) :
    Value models context (origins context) remaining keys (.source (root.demand.arguments position).1) where
  pattern := .var (index (GeneralNominalSourceFrontier.frontier context.state) (root.demand.arguments position).1)
  term := .leaf (index (GeneralNominalSourceFrontier.frontier context.state) (root.demand.arguments position).1)
  labelled := ⟨(initial_value (models := models) (keys := keys) source position).labelled.1,
    (initial_value (models := models) (keys := keys) source position).labelled.2.1,
    fun _name member => (List.mem_singleton.mp member) ▸ retained⟩
  allowed := ⟨.var _,fun _name member => (List.mem_singleton.mp member) ▸ retained⟩

theorem initial_site
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ position, (root.demand.arguments position).1 = (root.demand.arguments position).2)
    (retained : ∀ position, index (GeneralNominalSourceFrontier.frontier context.state)
      (root.demand.arguments position).1 ∈ remaining)
    (same : labels root = rootPatterns context root) :
    SiteValues models context remaining (keyMenu registry) (testMenu context registry)
      labels (rootSite context.state.seed root) := by
  let values : (position : Fin (roles root.demand.role).arity) →
      Value models context (origins context) remaining (keyMenu registry)
        (.source ((rootSite context.state.seed root).center position)) := fun position =>
    (root_value (models := models) (keys := keyMenu registry) source position (retained position)).alias
      (fun model _ => by
        rw [point_center context.state.seed root position (point position)]
        exact source_self model _)
  exact ⟨values,same,fun _ => trivial⟩

theorem initialized
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ position, (root.demand.arguments position).1 = (root.demand.arguments position).2)
    (remaining : List Nat) (distinct : remaining.Nodup)
    (retained : ∀ position, index (GeneralNominalSourceFrontier.frontier context.state)
      (root.demand.arguments position).1 ∈ remaining) :
    ∃ inventory : Inventory, inventory.holes = remaining ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory ∧
      ∃ journal : Journal context root (initial context root).erased inventory,
        Nonempty (Coverage registry context root (initial context root) inventory journal) := by
  have allowed : ∀ pattern ∈ rootPatterns context root, Allowed (keyMenu registry) remaining pattern := by
    intro pattern member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
    exact (root_value (models := fun _ => True) source position (retained position)).allowed
  obtain ⟨depth,bounded⟩ := encoded_args_bounded (rootPatterns context root)
    (fun pattern member => (allowed pattern member).1)
    (forest_uses _ (fun pattern member => (allowed pattern member).2))
  let inventory : Inventory :=
    ⟨remaining,[GeneralNominalPatternInventory.encodeList (rootPatterns context root)],depth⟩
  let journal : Journal context root (initial context root).erased inventory := {
    labels := fun _ => rootPatterns context root
    member := List.mem_singleton_self _
    rootLabels := root_labelled context root
    history := by intro packet member; cases member }
  refine ⟨inventory,rfl,⟨distinct,?_⟩,journal,⟨{
    identity := fun _ _ _ => rfl
    rawFacts := []
    rawReadbacks := []
    rawTrusted := .source
    rawInputs := by intro origin member; cases member
    centeredFacts := []
    centeredTrusted := .source
    legacyIncluded := by intro fact member; cases member
    sites := ?_
    inputs := by intro origin member; cases member
    binders := by intro origin member; cases member }⟩⟩
  · intro term member
    cases List.mem_singleton.mp member
    exact ⟨bounded_closed bounded,bounded⟩
  · intro site member
    cases List.mem_singleton.mp member
    exact initial_site source point retained rfl

end Yulang.GeneralNominalCenteredInitialInventories
