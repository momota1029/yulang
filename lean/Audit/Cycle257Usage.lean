import Yulang.GeneralDictionaryFiniteJournal257
import Yulang.GeneralDictionaryBinderGap257
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

example (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalState.Known (GeneralDictionaryLooseIterationBook240.context n).state (GeneralDictionaryLooseFamilyBase240.source n slot) ↔
 GeneralNominalState.Known (GeneralDictionaryLooseIterationBook240.context 0).state (GeneralDictionaryFiveSlot257.projection slot).val :=
 GeneralDictionaryKnownProjection257.preserved n slot
example (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalReobservationSteps.PointAt (GeneralDictionaryLooseIterationBook240.context n).state slot ↔
 GeneralNominalReobservationSteps.PointAt (GeneralDictionaryLooseIterationBook240.context 0).state (GeneralDictionaryFiveSlot257.projection slot) :=
 GeneralDictionaryPointProjection257.preserved n slot
example (n : Nat) : GeneralDictionaryReportProjection257.transport n
 (GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet n)) =
 GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet 0) :=
 GeneralDictionaryReportProjection257.actual_report n
example (n : Nat) : GeneralNominalState.Models
 (GeneralDictionaryLooseIterationIteration240.state (n+1)).core.erased.current.context.state
 (GeneralDictionaryBinderGap257.witness (n+1)) ∧
 ¬ GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1))
 (GeneralDictionaryBinderGap257.witness (n+1)) := GeneralDictionaryBinderGap257.current_raw_not_journal n

example (n : Nat) (a : Assignment) : GeneralNominalVersionedJournal232.Models
 (GeneralDictionaryLooseIterationIteration240.state (n+1)) a ↔
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context (n+1)).state a ∧
 GeneralDictionaryBinderFact257.Holds a := GeneralDictionaryJournalRepair257.exact n a
example (n : Nat) (a : Assignment) : (GeneralDictionaryFiniteJournal257.view (n+1)).Models a ↔
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1))
 (GeneralPresenceOrderedBlock247.solve model (GeneralDictionaryUpperHistory257.history (n+1)) a) :=
 GeneralDictionaryFiniteJournal257.solved_exact n a
example (n : Nat) (boundary : Assignment) :
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) a) ↔
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧ (GeneralDictionaryFiniteJournal257.view (n+1)).Models a) :=
 GeneralDictionaryFiniteJournal257.public_models n boundary
example (n : Nat) : (GeneralDictionaryFiniteJournal257.view n).ordinary.length ≤ 10 := GeneralDictionaryFiniteJournal257.ordinary_bound n
example (n : Nat) : GeneralDictionaryFiniteJournal257.view (n+1) = GeneralDictionaryFiniteJournal257.view 1 := GeneralDictionaryFiniteJournal257.stable n
example : GeneralNominalVersionedJournal232.Models GeneralDictionaryLooseLoopSource240.initial GeneralDictionaryBinderGap257.seed :=
 GeneralDictionaryBinderGap257.seed_models
