import Yulang.GeneralDictionaryCanonicalLocalOrder
import Yulang.GeneralDictionaryNominalCandidateOrderExamples

/-! Reachability of the shared input does not constrain an arbitrary executor's
returned state. This counterexample refutes the universal-in-executor order
claim, not order independence of a faithful saturating implementation. -/
namespace Yulang.GeneralDictionaryFinalOrderObstruction

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDeclarationExamples (roles constructors)
open GeneralDictionaryReachableBoundary
open GeneralDictionaryCanonicalLocalOrder

abbrev first := GeneralNominalExamples.registry
abbrev last := GeneralDictionaryNominalCandidateOrderExamples.reversed
abbrev root := GeneralNominalProgressObstruction.root 0
abbrev pendingSource := GeneralNominalState.embed GeneralNominalProgressObstruction.base
  GeneralNominalProgressObstruction.view constructors
abbrev pendingContext : GeneralNominalCandidates.Context := ⟨pendingSource,GeneralNominalExamples.interpretation⟩
abbrev input := initial pendingContext root
abbrev cyclic := initial GeneralNominalProgressObstruction.context root

theorem reorders : GeneralRegistryReordering.Reorders first last :=
  GeneralDictionaryNominalCandidateOrderExamples.visible_reversed

theorem first_checked : (boundary roles).Checked first := ⟨rfl,GeneralNominalExamples.registry_checked⟩
theorem last_checked : (boundary roles).Checked last :=
  ⟨rfl,GeneralDictionaryNominalCandidateOrderExamples.reversed_checked⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource first pendingContext root := by
  refine ⟨rfl,⟨rfl,?_⟩,?_,(by intro _ _ _; exact CommonNominalFullCarrier.subtype_refl _),?_,rfl⟩
  · intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive; exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · intro source member
    have bound := GeneralNominalAllocation.member_le_max (GeneralNominalState.sources pendingSource) source member
    exact Nat.le_trans bound (by decide +kernel)

theorem first_reachable : B4TargetV5.Reachable (boundary roles) first root input :=
  B4TargetV5.reachable_initial _ ⟨pendingContext,initial_source,rfl⟩

theorem last_reachable : B4TargetV5.Reachable (boundary roles) last root input :=
  B4TargetV5.reachable_initial _ (GeneralDictionaryInitialSource.initial_reorders first last reorders root input
    ⟨pendingContext,initial_source,rfl⟩)

theorem input_pending : GeneralNominalState.RootPending pendingSource root.demand := by
  refine ⟨⟨0,by decide +kernel⟩,?_⟩
  rintro ⟨slot,_,head | nominal⟩
  · exact head rfl
  · obtain ⟨d,recorded⟩ := nominal
    cases recorded

theorem pending_local : B4TargetV3.Local (boundary roles).toSourceBoundary first input root .pending :=
  .pending input_pending

theorem rejected_local : B4TargetV3.Local (boundary roles).toSourceBoundary last cyclic root .rejected := by
  apply (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    last cyclic root .rejected).mpr
  exact GeneralNominalFeedbackK2.root_rejected last cyclic root
    (Or.inl (GeneralNominalCycleRegressions.nominal_cycle_K2 0))

/-- Deliberately unconstrained run: no execution/halting obligation is claimed. -/
def executor : B4TargetV3.Executor (GeneralNominalFeedbackBoundary.vocabulary roles) where
  run registry _ _ :=
    (if registry.declarations.head?.map Declaration.id = some 3 then input else cyclic,.pending)

theorem first_returned : (executor.run first input root).1 = input := rfl
theorem last_returned : (executor.run last input root).1 = cyclic := rfl

theorem not_canonicalLocalOrder : ¬ CanonicalLocalOrder roles executor := by
  intro order
  have equivalent := order first last first_checked last_checked reorders input root first_reachable last_reachable root .pending
  rw [first_returned,last_returned] at equivalent
  have impossible := B4TargetV3.local_functional (equivalent.mp pending_local) rejected_local
  cases impossible

theorem not_all_executors :
    ¬ (∀ e : B4TargetV3.Executor (GeneralNominalFeedbackBoundary.vocabulary roles), CanonicalLocalOrder roles e) :=
  fun all => not_canonicalLocalOrder (all executor)

end Yulang.GeneralDictionaryFinalOrderObstruction
