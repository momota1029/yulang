import Yulang.GeneralRebaseFiniteCodeAcc277
import Yulang.GeneralDictionaryVersionLoopNontermination239

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFiniteCodeBoundary277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseFiniteCodeAcc277 (Certificate)
open GeneralRebaseQuietBound277 (Counted)
open GeneralRebaseMixedCounts277 (Actual)
variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {state : State roles}

theorem absorb_of_meaning (formed : Reachable r root state) {old next : Plan roles}
    (recorded : old ∈ state.plans)
    (meaning : ∀ m, Models state m →
      GeneralNominalVersionedPlans231.Holds old m →
      GeneralNominalVersionedEffects231.ClassEffects state.core old.packet.site.occurrence old m →
      GeneralNominalVersionedPlans231.Holds next m ∧
        GeneralNominalVersionedEffects231.ClassEffects state.core next.packet.site.occurrence next m)
    (retained : ∀ child ∈ GeneralNominalVersionedFrame231.children next.packet,
      ∃ equivalent ∈ GeneralNominalVersionedFrame231.children old.packet,
        (next.packet.site.occurrence,child) = (old.packet.site.occurrence,equivalent)) :
    Committed state next := by
  have oldReady := GeneralNominalVersionedMixedPlanLedger235.reachable_plan_committed formed recorded
  refine ⟨?_,?_⟩
  · intro m valid
    exact meaning m valid (oldReady.1 m valid).1 (oldReady.1 m valid).2
  · intro kid present
    obtain ⟨other,member,route⟩ := retained kid present
    exact route.symm ▸ oldReady.2 other member

namespace Loop
open GeneralDictionaryVersionLoopSource237 (sourceRegistry initial)

theorem formed : Reachable sourceRegistry GeneralDictionaryVersionLoopSource237.root initial :=
    ⟨initial,GeneralDictionaryVersionLoopInitial238.initial_source,.refl⟩

theorem no_finite_code (Key : Type) : ¬ Nonempty (Certificate sourceRegistry GeneralDictionaryVersionLoopSource237.root Key) := by
  rintro ⟨cert⟩
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc
    (GeneralRebaseFiniteCodeAcc277.accessible cert formed)

theorem no_installation_limit (K : Nat) :
    ¬ (∀ n last, Counted (Actual sourceRegistry GeneralDictionaryVersionLoopSource237.root) initial n last →
      last.plans.length ≤ initial.plans.length + K) := by
  intro limit
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc
    (GeneralRebaseBoundedInstallAcc277.adapter_accessible formed K limit)

theorem arbitrarily_many_installations (K : Nat) :
    ∃ n last, Counted (Actual sourceRegistry GeneralDictionaryVersionLoopSource237.root) initial n last ∧
      initial.plans.length + K < last.plans.length := by
  classical
  apply Classical.byContradiction
  intro noWitness
  apply no_installation_limit K
  intro n last trace
  by_cases within : last.plans.length ≤ initial.plans.length + K
  · exact within
  · exact False.elim (noWitness ⟨n,last,trace,Nat.lt_of_not_ge within⟩)

end Loop
end Yulang.GeneralRebaseFiniteCodeBoundary277
