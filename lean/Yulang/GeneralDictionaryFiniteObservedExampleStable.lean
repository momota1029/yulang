import Yulang.GeneralDictionaryFiniteObservedExample
import Yulang.GeneralDictionarySupportRecursiveClosure

/-! The inhabited ternary named-output source is already stable: its closed
output schema is entailed before any packet installation. No nontrivial
transition is asserted by this zero-step execution regression. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleStable
open GeneralDictionaryFiniteObservedExample
open GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)

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
  change arguments context psite.occurrence = some pbounds at found
  change psite.occurrence = root at same
  rw [same] at found
  have located : arguments context root = some [((1 : Fin 2),(1 : Fin 2))] := by decide +kernel
  have equal := Option.some.inj (found.symm.trans located)
  subst pbounds
  constructor
  · intro m valid
    change BranchModels registry context psite.occurrence declaration pchecked [(1,1)] m
    rw [same]
    exact branch_models m valid.1
  · intro c member
    have empty := GeneralDictionaryLinearLeaf.children_empty context registry psite.occurrence declaration pchecked rfl
      (bindings state (report context declaration [(1,1)]))
    change c ∈ GeneralNominalAllocation.children context.state registry psite.occurrence declaration pchecked
      (bindings state (report context declaration [(1,1)])) at member
    rw [empty] at member
    cases member

abbrev varying (name : Nat) : GeneralNominalCommonBridge.Assignment := fun source =>
  if source = name then (.base .str,Common.rowEmpty) else model source

theorem varying_source (name : Nat) (large : 2 ≤ name) : GeneralNominalState.Models state (varying name) := by
  have low : ∀ slot : Fin 2, varying name slot.val = model slot.val := by
    intro slot
    simp [varying,show slot.val ≠ name by omega]
  have assigned : GeneralNominalCommonBridge.assignment state.base (varying name) =
      GeneralNominalCommonBridge.assignment state.base model := by
    funext slot; exact low slot
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state.base (varying name)) _
    rw [assigned]
    exact state_models.1.1
  · intro slot term recorded
    have original := state_models.1.2.1 slot term recorded
    change Equivalent (varying name slot.val).1 (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state.base (varying name)))
    rw [low slot,assigned]
    exact original
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := state_models.2.1 slot descriptor recorded
    refine ⟨values,?_,?_⟩
    · have transform : ∀ parameters values, GeneralNominalState.FitsAll state.base model parameters values → GeneralNominalState.FitsAll state.base (varying name) parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values head tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> first | exact head | simpa [GeneralNominalState.Fits,low] using head
      exact transform _ _ fits
    · simpa [low] using equal

theorem refresh_large_unknown (next : Context)
    (certificate : GeneralNominalCycleSteps.Refresh start.current next) (id : Nat) (large : 2 ≤ id) :
    ¬ GeneralNominalState.Known next.state id :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying id) id
    (by change (if id = 0 then nominal 0 arguments else .base .int) = .base .int; exact ite_eq_right (by omega))
    (by simp only [varying,ite_true]; rfl)
    (certificate.exact _ (initial_models model state_models)) (certificate.exact _ (initial_models _ (varying_source id large)))

theorem point_closed : GeneralNominalReobservationSteps.PointClosed state := by
  intro slot desc recorded
  change (if slot = (0 : Fin 2) then some descriptor else none) = some desc at recorded
  by_cases zero : slot = (0 : Fin 2)
  · subst slot
    have same := Option.some.inj recorded
    subst desc
    intro parameter member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · simp [zero] at recorded

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

theorem stable_reachable_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    Models start.current model ∧ GeneralNominalSupportSteps.Stable registry start root ∧
    root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id []) :=
  ⟨actual_reachable,initial_models model state_models,stable,named_request_present,fun m valid => full_evidence m valid.1⟩
end Yulang.GeneralDictionaryFiniteObservedExampleStable
