import Yulang.GeneralDictionaryProjectionBoundary257
import Yulang.GeneralDictionaryCompactView257
import Yulang.GeneralDictionaryLooseIterationNontermination240
open Yulang
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
example (n : Nat) : GeneralPresenceDefinitionRewrite244.block
 (GeneralDictionaryUpperHistory257.history n) ⊆ GeneralDictionaryLooseIterationBook240.atoms n :=
 GeneralDictionaryUpperHistory257.block_in_source n
example (n : Nat) : B4TargetV8.Reachable
 (GeneralNominalPointSourceBoundary240.boundary GeneralDictionaryLooseLoopSource240.roles)
 GeneralDictionaryLooseLoopSource240.sourceRegistry GeneralDictionaryLooseLoopSource240.root
 (GeneralDictionaryLooseIterationIteration240.state n) := GeneralDictionaryReachableAggregate256.reachable_all n
example (n : Nat) : (GeneralDictionaryOrdinaryCanonical257.compact n).length ≤ 4 :=
 GeneralDictionaryOrdinaryCanonical257.length_bound n
example (n : Nat) : (GeneralDictionaryOrdinaryFinite257.rewritten n).length = 16*n :=
 GeneralDictionaryOrdinaryFinite257.length_rewritten n
example (n : Nat) : GeneralDictionaryOrdinaryCanonical257.compact (n+1) =
 GeneralDictionaryOrdinaryFinite257.candidates := GeneralDictionaryOrdinaryCanonical257.stable n
example (n : Nat) (a : Assignment) : (GeneralDictionaryCompactView257.compact n).Models a ↔
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state
 (GeneralPresenceOrderedBlock247.solve model (GeneralDictionaryUpperHistory257.history n) a) :=
 GeneralDictionaryCompactView257.compact_solved n a
example (n : Nat) (boundary : Assignment) :
 (∃ a, GeneralNominalRebasePublicModel242.PublicAgree (GeneralDictionaryCompactView257.hidden n) a boundary ∧
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state a) ↔
 (∃ a, GeneralNominalRebasePublicModel242.PublicAgree (GeneralDictionaryCompactView257.hidden n) a boundary ∧
 (GeneralDictionaryCompactView257.compact n).Models a) := GeneralDictionaryCompactView257.public_models n boundary
example (n : Nat) : GeneralPresenceCheckedNormal252.prepare .lower
 [.var 0,.var 1,.var 2,.var 3,.var 4]
 (GeneralPresenceOrderedSubstitution247.mapping (GeneralDictionaryUpperHistory257.history (n+1))
 (GeneralDictionaryLooseFamilyNames240.upper n)).ty = none :=
 GeneralDictionaryFullReduced257.lower_adapter_failure (n+1) n (by omega)
example (n : Nat) : GeneralPresenceCheckedNormal252.prepare .lower
 [.var 0,.var 1,.var 2,.var 3,.var 4]
 (GeneralPresenceIdempotentTree257.reduce
 (GeneralPresenceOrderedSubstitution247.mapping (GeneralDictionaryUpperHistory257.history (n+1))
 (GeneralDictionaryLooseFamilyNames240.upper n)).ty) = some (.var 4) :=
 GeneralDictionaryFullReduced257.repaired_upper_prepare (n+1) n (by omega)
example (n : Nat) : (GeneralDictionaryCompactView257.compact n).slots = n+5 :=
 GeneralDictionaryCompactView257.slot_count n
#check GeneralDictionaryLooseIterationNontermination240.initial_no_acc

example (n : Nat) (a : Assignment) : (GeneralDictionaryCompactView257.compact n).Models a ↔
 (GeneralDictionaryFiveSlot257.view n).Models a := GeneralDictionaryFiveSlot257.models_exact n a
example (n : Nat) : (GeneralDictionaryFiveSlot257.view n).slots = 5 := GeneralDictionaryFiveSlot257.five_slots n
example (n : Nat) : (GeneralDictionaryFiveSlot257.view n).ordinary.length ≤ 8 := GeneralDictionaryFiveSlot257.ordinary_bound n
example (n : Nat) : GeneralNominalViewTypeTerms255.terms (GeneralDictionaryFiveSlot257.view n) ⊆
 GeneralDictionaryFiniteView257.pool := GeneralDictionaryFiniteView257.terms_finite n
example (n : Nat) (a : Assignment) : (GeneralDictionaryFiveSlot257.view n).Models a ↔
 (GeneralDictionaryFiveSlot257.view 0).Models a := GeneralDictionaryNoModelRefinement257.all_iff_zero n a
example (n : Nat) (boundary : Assignment) :
 (∃ a, GeneralDictionaryInitialProjection257.Agree a boundary ∧
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state a) ↔
 (∃ a, GeneralDictionaryInitialProjection257.Agree a boundary ∧
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context 0).state a) :=
 GeneralDictionaryNoModelRefinement257.initial_public_models n boundary
example (n : Nat) : ¬ Function.Injective (@GeneralDictionaryFiveSlot257.projection (n+1)) :=
 GeneralDictionaryProjectionBoundary257.not_injective n
example (n : Nat) : GeneralDictionaryLooseIterationIteration240.state (n+1) ≠
 GeneralDictionaryLooseIterationIteration240.state (n+2) ∧
 GeneralDictionaryFiveSlot257.view (n+1) = GeneralDictionaryFiveSlot257.view (n+2) :=
 GeneralDictionaryProjectionBoundary257.distinct_with_same_view n
example (rank : GeneralNominalRebaseRawView243.View → Nat) :
 ¬ ∀ n, rank (GeneralDictionaryFiveSlot257.view (n+2)) < rank (GeneralDictionaryFiveSlot257.view (n+1)) :=
 GeneralDictionaryFiniteView257.no_strict_view_rank rank
