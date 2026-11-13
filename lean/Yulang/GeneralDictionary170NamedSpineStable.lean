import Yulang.GeneralDictionary170NamedSpineExample
import Yulang.GeneralDictionary169SharedStable

/-! The nominal-input named-output coverage gap persists at actual Shared
stability. This is a zero-step initial source, not a new nonterminal execution. -/
namespace Yulang.GeneralDictionary170NamedSpineStable
open GeneralDictionary170NamedSpineExample
open GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)
private abbrev state := source
private abbrev model := GeneralDictionaryFiniteObservedExample.model
private abbrev arguments := GeneralDictionaryFiniteObservedExample.arguments
private abbrev descriptor := GeneralDictionaryFiniteObservedExample.descriptor
private abbrev state_models := GeneralDictionaryFiniteObservedExample.state_models
private abbrev varying := GeneralDictionaryFiniteObservedExampleStable.varying
private abbrev varying_source := GeneralDictionaryFiniteObservedExampleStable.varying_source
private abbrev point_closed := GeneralDictionaryFiniteObservedExampleStable.point_closed

theorem initial_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state m) : Models start.current m :=
  (GeneralNominalSaturationState.initial_models context root m).mpr valid

theorem generated_root (focus : GeneralSourceDictionaries.Occurrence roles)
    (reached : Generated start.current root focus) : focus = root := by
  induction reached with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    subst same
    rfl

theorem installs_committed (p : Packet roles)
    (reached : Generated start.current root p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry start.current p) :
    GeneralNominalFeedbackSteps.Committed start.current p := by
  have same := generated_root _ reached
  rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
  have reg := enabled.1.1
  have ctx := enabled.1.2.1
  dsimp only at reg ctx
  subst preg; subst pctx
  have visible := enabled.1.2.2.2.1
  have decl := List.mem_singleton.mp visible
  change pdecl = declaration at decl
  subst pdecl
  have found := enabled.1.2.2.2.2.2.1
  change GeneralNominalRecursiveCandidates.arguments context psite.occurrence = some pbounds at found
  change psite.occurrence = root at same
  rw [same] at found
  have located : GeneralNominalRecursiveCandidates.arguments context root = some [((0 : Fin 2),(0 : Fin 2))] := by decide +kernel
  have equal := Option.some.inj (found.symm.trans located)
  subst pbounds
  constructor
  · intro m valid
    change BranchModels registry context psite.occurrence declaration pchecked [(0,0)] m
    rw [same]
    exact GeneralDictionary170NamedSpine.branch_models context registry root declaration pchecked shape m valid.1
  · intro c member
    have empty := GeneralDictionaryLinearLeaf.children_empty context registry psite.occurrence declaration pchecked rfl
      (bindings state (report context declaration [(0,0)]))
    change c ∈ GeneralNominalAllocation.children context.state registry psite.occurrence declaration pchecked
      (bindings state (report context declaration [(0,0)])) at member
    rw [empty] at member
    cases member

theorem refresh_large_unknown (next : Context)
    (certificate : GeneralNominalCycleSteps.Refresh start.current next) (id : Nat) (large : 2 ≤ id) :
    ¬ GeneralNominalState.Known next.state id :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying id) id
    (by change (if id = 0 then nominal 0 arguments else .base .int) = .base .int; exact ite_eq_right (by omega))
    (by simp only [varying,GeneralDictionaryFiniteObservedExampleStable.varying,ite_true]; rfl)
    (certificate.exact _ (initial_models model state_models)) (certificate.exact _ (initial_models _ (varying_source id large)))

theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry start.current root := by
  intro focus generated next update
  cases update with
  | enqueue focus _ absent =>
    exact absent (GeneralNominalDemandMerging.pointSite root) (List.mem_singleton_self _) (generated_root focus generated).symm
  | install p enabled novel => exact novel (installs_committed p generated enabled)
  | merge first last one two _ novel =>
    have one := List.mem_singleton.mp one
    have two := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ next certificate id _ unknown known =>
    by_cases zero : id = 0
    · subst id
      exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨descriptor,rfl⟩⟩
    · by_cases one : id = 1
      · subst id
        exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩
      · exact refresh_large_unknown next certificate id (by omega) known
  | equate _ first last _ _ equal novel =>
    exact novel (fun m valid => equal m (initial_models m valid))

theorem stable : GeneralNominalSupportSteps.Stable registry start root := by
  intro focus generated next update
  have old := GeneralNominalSupportSteps.at_old update
  exact (GeneralNominalReobservationSteps.stable_of_pointClosed feedback_stable point_closed) focus generated _ old


theorem shared_stable : GeneralNominalSharedSteps.Stable registry start root := by
  apply GeneralDictionary169SharedStable.of_value
  intro focus reached next update
  exact stable focus reached next
    (GeneralNominalDownstreamSteps.at_old (GeneralNominalValueSteps.at_old update))

theorem stable_coverage_gap :
    GeneralNominalSharedSteps.SourceFormed registry root start ∧
    GeneralNominalSharedSteps.Stable registry start root ∧
    Models start.current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) ∧
    ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry start root) :=
  ⟨.initial context initial_source,shared_stable,initial_models model state_models,
    actual_evidence model state_models,no_current_local_node⟩
end Yulang.GeneralDictionary170NamedSpineStable
