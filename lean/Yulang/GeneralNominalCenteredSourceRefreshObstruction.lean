import Yulang.GeneralNominalCenteredSourceRefreshWitness
import Yulang.GeneralNominalCenteredSourceLiveProduction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalCenteredSourceRefreshObstruction
open GeneralNominalCenteredSourceRefreshWitness
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredSourceInvariant
open GeneralNominalCenteredSourceLiveReadbacks GeneralNominalCanonicalHoleJournal
open GeneralNominalHoleElimination GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalOpenPatternLabels GeneralNominalCanonicalPacketTransport

abbrev fullHoles := GeneralNominalIndexedHoleReadback.holes (GeneralNominalSourceFrontier.frontier source)
abbrev rootPattern : Pattern := .app 5 [.var 1,.var 2]
abbrev rootTree : Expr Nat := .node (.structural .pair) (fun i => .leaf (if i.val = 0 then 1 else 2))
def labels (occurrence : Occurrence roles) : List Pattern :=
  if occurrence.identity = root.identity then [rootPattern] else [.var 1]
theorem root_label : Label context rootPattern rootTree := by
  refine ⟨rfl,?_,⟨trivial,fun _ => trivial⟩⟩
  simp [rootPattern,rootTree,GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote,List.ofFn_succ,interpretation,constructors,GeneralDeclarationExamples.constructors]

theorem root_allowed : GeneralNominalSourceLabelVocabulary.Allowed (keyMenu registry) fullHoles rootPattern := by
  constructor
  · exact .app (by decide +kernel) (by intro pattern member; rcases List.mem_cons.mp member with rfl|member; exact .var _; cases List.mem_singleton.mp member; exact .var _)
  · intro name member
    have mem : name = 1 ∨ name = 2 := by simpa [rootPattern,Pattern.variables,variablesArgs] using member
    rcases mem with rfl|rfl <;> decide +kernel

theorem root_readback : GeneralNominalIndexedHoleReadback.Readback
    (GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites [])
    (origins context) fullHoles (.source 0) rootTree := by
  constructor
  · intro model valid
    have schema := headSchemaP_holds model valid.1
    rw [headSchemaP_exact] at schema
    constructor
    · exact schema.1 _ (List.mem_singleton_self _)
    · intro i
      have parts : i.val = 0 ∨ i.val = 1 := by have := i.isLt; change i.val < 2 at this; omega
      rcases parts with zero|one
      · have found := schema.2 ⟨0,.structural (.source 0) .pair 0,.actual⟩ (List.mem_cons_self ..)
        rw [binderP_zero] at found
        simpa [GeneralNominalIndexedHoleReadback.interpret,rootTree,Expr.bind,zero,origins,
          GeneralNominalIndexedHoleReadback.origin,GeneralNominalSourceFrontier.frontier,
          GeneralNominalState.sources,Holds,project] using found
      · have found := schema.2 ⟨1,.structural (.source 0) .pair 1,.actual⟩ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        rw [binderP_one] at found
        simpa [GeneralNominalIndexedHoleReadback.interpret,rootTree,Expr.bind,one,origins,
          GeneralNominalIndexedHoleReadback.origin,GeneralNominalSourceFrontier.frontier,
          GeneralNominalState.sources,Holds,project] using found
  · intro name member
    have mem : name = 1 ∨ name = 2 := by simpa [rootTree,Expr.leaves,List.ofFn_succ] using member
    rcases mem with rfl|rfl <;> decide +kernel

def rootValue : Value (GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites [])
    context (origins context) fullHoles (keyMenu registry) (.source 0) :=
  ⟨rootPattern,rootTree,⟨root_label,root_readback⟩,root_allowed⟩

theorem root_vocabulary : Vocabulary (testMenu context registry) rootTree := by
  exact ⟨by simp [normalize,normalizeArgs,testMenu,sourceMenu,GeneralNominalSchemaBudget.menu,GeneralNominalSchemaVocabulary.vocabulary,GeneralNominalInspection.translate,interpretation,constructors,GeneralDeclarationExamples.constructors],fun _ => trivial⟩

theorem child_identity : emittedChild.occurrence.identity ≠ root.identity := by
  have bound := GeneralNominalIdentityJournal.child_parent packetP childR childSignature
  change root.identity < emittedChild.occurrence.identity at bound
  omega

def presentP : Presentation context labels packetP where
  capture := fun name => .var (if name = 0 then 1 else 2)
  trees := fun name => .leaf (if name = 0 then 1 else 2)
  captureLabels := fun _ => ⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],trivial⟩
  coveredHead := rfl
  head := by
    refine .cons ?_ .nil
    refine ⟨rootTree,root_label,?_⟩
    have query : GeneralNominalInspection.translate context.state.constructors context.interpretation (normalize (.app 5 [.var 0,.var 1])) =
        .node .pair (List.ofFn (fun i : Fin 2 => .variables [i.val])) := by
      simp [GeneralNominalInspection.translate,normalize,normalizeArgs,List.ofFn_succ,interpretation,constructors,GeneralDeclarationExamples.constructors]
    rw [query]
    apply GeneralNominalHeadMatchMass.Matches.structural
    intro i
    have parts : i.val = 0 ∨ i.val = 1 := by have := i.isLt; change i.val < 2 at this; omega
    rcases parts with zero|one
    · have eq : i = (0 : Fin 2) := Fin.ext zero
      subst i
      exact .capture .refl
    · have eq : i = (1 : Fin 2) := Fin.ext one
      subst i
      exact .capture .refl
  children := by
    intro clause member signature
    cases List.mem_singleton.mp member
    change (if (GeneralNominalFeedbackSites.clauseChild packetP childR signature).identity = root.identity
      then [rootPattern] else [.var 1]) = [.var 1]
    have different : (GeneralNominalFeedbackSites.clauseChild packetP childR signature).identity ≠ root.identity := child_identity
    simp only [different,ite_false]

structure LiveStart where
  inventory : Inventory
  holes : inventory.holes = fullHoles
  valid : Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) inventory
  journal : Journal context root refreshed.erased inventory
  coverage : Coverage' registry context root refreshed inventory journal
  facts : coverage.centeredFacts = []

theorem liveStart_exists : Nonempty LiveStart := by
  obtain ⟨depth,bounded⟩ := GeneralNominalSourceLabelVocabulary.encoded_args_bounded [rootPattern]
    (by intro pattern member; cases List.mem_singleton.mp member; exact root_allowed.1)
    (by intro name member; exact root_allowed.2 name (by simpa [variablesArgs] using member))
  let inventory : Inventory := ⟨fullHoles,[GeneralNominalPatternInventory.encodeList [rootPattern]],depth⟩
  let journal : Journal context root refreshed.erased inventory := {
    labels := labels
    member := List.mem_singleton_self _
    rootLabels := by
      intro pattern member
      have same : pattern = rootPattern := List.mem_singleton.mp member
      subst pattern
      exact ⟨rootTree,root_label⟩
    history := by
      intro packet member _
      have same : packet = packetP := List.mem_singleton.mp member
      subst packet
      exact ⟨presentP⟩ }
  let coverage : Coverage' registry context root refreshed inventory journal := {
    identity := by intro first last same; change labels first = labels last; unfold labels; rw [same]
    rawFacts := []
    rawReadbacks := []
    rawTrusted := .source
    rawInputs := by intro origin member; cases member
    centeredFacts := []
    centeredTrusted := .source
    legacyIncluded := by intro fact member; cases member
    sites := by
      intro site member
      have members : site = rootSite source.seed root ∨ site = emittedChild := by
        simpa [refreshed,GeneralNominalCenteredSteps.refresh,afterP,GeneralNominalCenteredSteps.install,
          GeneralNominalCenteredSteps.initial,GeneralNominalCenteredSteps.administrative,GeneralNominalCenteredSteps.initialAt,Plan.emitted] using member
      rcases members with rfl|rfl
      · refine ⟨fun _ => rootValue,rfl,fun _ => root_vocabulary⟩
      · let value : Value (GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites [])
          context (origins context) fullHoles (keyMenu registry) (.source 1) :=
          frontier_value (GeneralNominalSourceFrontier.source_member
            (GeneralNominalAllocationSupport.slot_source source (1 : Fin 4)))
        refine ⟨fun position => value.alias (fun model _ => ?_),?_,fun _ => trivial⟩
        · rw [childP_center childSignature position]
          exact source_self model 1
        · simp only [journal,labels,child_identity,ite_false]
          rfl
    inputs := by intro origin member; cases member
    binders := by intro origin member; cases member
    retention := Retention.full context root refreshed rfl }
  refine ⟨⟨inventory,rfl,?_,journal,coverage,rfl⟩⟩
  refine ⟨List.nodup_range,?_⟩
  intro term member
  cases List.mem_singleton.mp member
  exact ⟨GeneralNominalSourceLabelVocabulary.bounded_closed bounded,bounded⟩

noncomputable def liveStart : LiveStart := Classical.choice liveStart_exists

noncomputable def refreshJob : GeneralNominalCenteredInstallObligations.Installation registry context root where
  state := refreshed
  reachable := refreshed_reachable
  inventory := liveStart.inventory
  valid := liveStart.valid
  journal := liveStart.journal
  coverage := liveStart.coverage.toCoverage
  plan := planR
  support := []
  generated := generatedR
  enabled := enabledR
  novel := novelR
  guard := guardR
  children := by decide +kernel

theorem not_input_readback_and_origins :
    ¬ GeneralNominalCenteredSourceLiveProduction.InputReadbackAndOrigins' registry context root := by
  intro produce
  have readback := (produce refreshJob liveStart.coverage.retention).1
  change GeneralNominalCenteredSupport.Readback refreshed.erased refreshed.sourceSites
    liveStart.coverage.centeredFacts planR at readback
  rw [liveStart.facts] at readback
  exact no_empty_readbackR readback

theorem unknown_input : ¬ GeneralNominalState.Known source 2 := by
  rintro ⟨slot,equal,known⟩
  have same : slot = (2 : Fin 4) := Fin.ext equal
  subst slot
  rcases known with impossible | ⟨descriptor,recorded⟩
  · exact impossible rfl
  · cases recorded

theorem strengthened_counterexample :
    Checked registry ∧ GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧
      B4Target.Steps (Step registry root) initialState refreshed ∧
      Step registry root refreshed afterR ∧
      liveStart.inventory.holes = fullHoles ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests (keyMenu registry)) liveStart.inventory ∧
      Nonempty (Coverage' registry context root refreshed liveStart.inventory liveStart.journal) ∧
      ¬ GeneralNominalCenteredSourceLiveProduction.InputReadbackAndOrigins' registry context root :=
  ⟨checked,initial_source,point,refreshed_reachable,stepR,liveStart.holes,liveStart.valid,⟨liveStart.coverage⟩,not_input_readback_and_origins⟩

end Yulang.GeneralNominalCenteredSourceRefreshObstruction

