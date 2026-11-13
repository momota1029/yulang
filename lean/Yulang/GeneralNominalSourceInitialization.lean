import Yulang.GeneralNominalCaptureComparison

/-! Initial unknown inputs have a concrete finite journal. Inconsistent
reachable states terminate through the existing administrative order. -/
namespace Yulang.GeneralNominalSourceInitialization
open GeneralDeclarationPatterns GeneralNominalSourceLabelVocabulary
open GeneralNominalHoleElimination GeneralNominalIndexedHoleReadback
open GeneralNominalCanonicalHoleJournal GeneralNominalSupport GeneralSourceDictionaries
open GeneralNominalOpenPatternLabels GeneralNominalLabelledOriginClosure
open GeneralNominalOriginTerms GeneralNominalActualInspectionSteps GeneralNominalSaturationState

variable {roles : Roles.RoleDecls}

def rootPatterns (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : List Pattern :=
  List.ofFn fun position => .var
    (index (GeneralNominalSourceFrontier.frontier context.state) (root.demand.arguments position).1)

theorem root_allowed
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) :
    ∀ pattern ∈ rootPatterns context root,
      Allowed keys (holes (GeneralNominalSourceFrontier.frontier context.state)) pattern := by
  intro pattern member
  obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
  exact (initial_value (models := fun _ => True) (keys := keys) source position).allowed

theorem root_labelled (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    ∀ pattern ∈ rootPatterns context root, ∃ term, Label context pattern term := by
  intro pattern member
  obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
  exact ⟨.leaf (index (GeneralNominalSourceFrontier.frontier context.state) (root.demand.arguments position).1),rfl,by
    simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],trivial⟩

theorem forest_uses (patterns : List Pattern)
    (known : ∀ pattern ∈ patterns, GeneralPatternVariableProvenance.Uses allowed pattern) :
    ∀ name ∈ variablesArgs patterns, allowed name := by
  induction patterns with
  | nil => intro name member; cases member
  | cons first rest ih =>
    intro name member
    rcases List.mem_append.mp member with one | two
    · exact known first (List.mem_cons_self ..) name one
    · exact ih (fun p h => known p (List.mem_cons_of_mem _ h)) name two

theorem initial_journal
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (keys : List Nat) :
    ∃ inventory : Inventory,
      inventory.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length ∧
      Valid (GeneralNominalSourceLabelVocabulary.tests keys) inventory ∧
      ∃ journal : Journal context root (GeneralNominalSupport.initial context root) inventory,
        journal.labels root = rootPatterns context root := by
  obtain ⟨depth,bounded⟩ := encoded_args_bounded (rootPatterns context root)
    (fun pattern member => (root_allowed (keys := keys) source pattern member).1)
    (forest_uses _ (fun pattern member => (root_allowed (keys := keys) source pattern member).2))
  let inventory : Inventory :=
    ⟨holes (GeneralNominalSourceFrontier.frontier context.state),
      [GeneralNominalPatternInventory.encodeList (rootPatterns context root)],depth⟩
  refine ⟨inventory,rfl,⟨List.nodup_range,?_⟩,?_⟩
  · intro term member
    cases List.mem_singleton.mp member
    exact ⟨bounded_closed bounded,bounded⟩
  · exact ⟨{
      labels := fun _ => rootPatterns context root
      member := List.mem_singleton_self _
      rootLabels := root_labelled context root
      history := by intro packet member; cases member },rfl⟩

theorem initial_trusted_inputs (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (origins : Nat → GeneralNominalRecursiveInspection.Origin) (remaining keys : List Nat)
    (tests : List GeneralNominalRecursiveInspection.Test) :
    GeneralNominalSourceProducerHandoff.TrustedInputs (initial context root) [] context origins remaining keys tests := by
  intro actual member
  cases member

theorem installable_inhabited (enabled : GeneralNominalFeedbackSteps.Installable registry state packet) :
    ∃ model, GeneralNominalSaturationState.Models state model := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  exact ⟨model,valid⟩

theorem inconsistent_accessible
    (formed : SourceFormed registry (root : Occurrence roles) state)
    (empty : ¬ ∃ model, GeneralNominalSaturationState.Models state.current model) :
    Acc (fun next current => Step registry root current next) state := by
  have all (state : Tracked roles) (accessible : Acc (fun next current => GeneralNominalSharedSteps.Passive registry current next) state) :
      SourceFormed registry root state →
      (¬ ∃ model, GeneralNominalSaturationState.Models state.current model) →
      Acc (fun next current => Step registry root current next) state := by
    induction accessible with
    | intro before predecessors ih =>
      intro formed empty
      refine Acc.intro before ?_
      intro after step
      rcases GeneralNominalActualBudget.formed_step_cases formed step with passive | ⟨packet,support,generated,enabled,novel,guard,equal⟩
      · exact ih after passive (.update formed step) (fun ⟨model,valid⟩ =>
          empty ⟨model,GeneralNominalSharedSteps.step_models (step_shared step) model valid⟩)
      · exact False.elim (empty (installable_inhabited enabled))
  exact all state (GeneralNominalSharedSteps.passive_accessible registry state) formed empty

theorem reachable_inconsistent_accessible
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : ¬ ∃ model, GeneralNominalSaturationState.Models state.current model) :
    Acc (fun next current => Step registry root current next) state :=
  inconsistent_accessible (GeneralNominalActualTraceSupport.formed_trace (.initial context source) path) empty

end Yulang.GeneralNominalSourceInitialization
