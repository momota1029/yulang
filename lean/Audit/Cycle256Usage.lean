import Yulang.GeneralNominalOrderedRawPublic256
import Yulang.GeneralDictionarySlotView256
import Yulang.GeneralNominalInitialAggregate256
import Yulang.GeneralDictionaryAggregateBasis256
import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralDictionaryLooseIterationNontermination240
open Yulang
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

-- A genuine initial source frame, including the associated-output fixture.
example : GeneralNominalFrameAggregate256.pairs GeneralDictionaryOutputDepth252.plan 0 ≠ [] :=
 GeneralNominalFrameAggregate256.nonempty GeneralDictionaryOutputDepth252.frame 0 (by decide)

example (labels : List GeneralDeclarationPatterns.Pattern) :
 GeneralNominalHistoricalAggregate256.prepare
 (GeneralNominalSourcePublicBasis255.basis GeneralDictionaryOutputDepth252.registry
   GeneralDictionaryOutputDepth252.context GeneralDictionaryOutputDepth252.root labels) []
 (GeneralNominalFrameAggregate256.pairs GeneralDictionaryOutputDepth252.plan 0) =
 some (GeneralNominalHistoricalAggregate256.rewrite
 (GeneralNominalSourcePublicBasis255.basis GeneralDictionaryOutputDepth252.registry
   GeneralDictionaryOutputDepth252.context GeneralDictionaryOutputDepth252.root labels) []
 (GeneralNominalFrameAggregate256.pairs GeneralDictionaryOutputDepth252.plan 0)) :=
 GeneralNominalInitialAggregate256.prepared _ _ labels GeneralDictionaryOutputDepth252.frame 0 (by decide)

-- Every stage is genuinely source reachable; no arbitrary-endpoint hypothesis.
example (n : Nat) : B4TargetV8.Reachable
 (GeneralNominalPointSourceBoundary240.boundary GeneralDictionaryLooseLoopSource240.roles)
 GeneralDictionaryLooseLoopSource240.sourceRegistry GeneralDictionaryLooseLoopSource240.root
 (GeneralDictionaryLooseIterationIteration240.state n) := GeneralDictionaryReachableAggregate256.reachable_all n

example (n : Nat) : GeneralNominalVersionedEvidence231.Frame GeneralDictionaryLooseLoopSource240.registry
 (GeneralDictionaryLooseIterationIteration240.state n).core GeneralDictionaryLooseLoopSource240.root 0
 (GeneralDictionaryLooseIterationBook240.plan n) := GeneralDictionaryReachableAggregate256.frame n

example (n : Nat) : GeneralNominalHistoricalAggregate256.prepare GeneralDictionaryAggregateHistory256.pool
 (GeneralDictionaryAggregateHistory256.history n)
 (GeneralNominalFrameAggregate256.pairs (GeneralDictionaryLooseIterationBook240.plan n) 0) =
 some GeneralDictionaryReachableAggregate256.representative := GeneralDictionaryAggregateHistory256.prepared n

example (n : Nat) : GeneralPresenceDefinitionRewrite244.block (GeneralDictionaryAggregateHistory256.history n) ⊆
 GeneralDictionaryLooseIterationBook240.atoms n := GeneralDictionaryAggregateHistory256.block_in_source n

example (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) assignment)
 (actual : Ty) : GeneralDictionaryReachableAggregate256.representative.Fits assignment actual ↔
 ∀ pair ∈ GeneralNominalFrameAggregate256.pairs (GeneralDictionaryLooseIterationBook240.plan n) 0,
 GeneralNominalCaptureMerges.Fits assignment pair actual := GeneralDictionaryReachableAggregate256.fits_exact n assignment valid actual

example (labels : List GeneralDeclarationPatterns.Pattern) : GeneralDictionaryAggregateHistory256.pool ⊆
 GeneralNominalSourcePublicBasis255.basis GeneralDictionaryLooseLoopSource240.registry
 GeneralDictionaryLooseLoopSource240.context GeneralDictionaryLooseLoopSource240.root labels :=
 GeneralDictionaryAggregateBasis256.initial_basis labels

example (n : Nat) : (GeneralDictionaryLooseIterationIteration240.state n).core.erased.current.context.state.base.slots = n+5 :=
 GeneralDictionaryLooseIterationIteration240.slots n

-- Finite aggregate representatives do not by themselves change the old Step.
example : ¬ Acc GeneralDictionaryLooseIterationNontermination240.reverseStep GeneralDictionaryLooseLoopSource240.initial :=
 GeneralDictionaryLooseIterationNontermination240.initial_no_acc

-- Empty occurrences are rejected only by this internal adapter; real input frames exclude them.
example : GeneralNominalHistoricalAggregate256.prepare [.var 2,.var 4] [] [] = none := rfl
example : GeneralNominalHistoricalAggregate256.prepare [.var 2,.var 4] [] [(2,4),(2,4)] =
 some GeneralDictionaryReachableAggregate256.representative := rfl

-- Roles stay separate: crossing the connective remains a failed support check.
example : GeneralPresenceCheckedNormal252.prepare .lower [.var 2,.var 4] (.inter (.var 2) (.var 4)) = none := by decide
example : GeneralPresenceCheckedNormal252.prepare .upper [.var 2,.var 4] (.union (.var 2) (.var 4)) = none := by decide

-- All actual base slot types, not just the current capture, have a finite menu.
example (n : Nat) (slot : Fin (n+5)) :
 GeneralPresenceCheckedNormal252.prepare .lower GeneralDictionaryHistoricalFields256.pool
   (((GeneralNominalRebaseRawView243.compile (GeneralDictionaryLooseIterationBook240.context n).state
     (GeneralPresenceOrderedSubstitution247.mapping (GeneralDictionaryAggregateHistory256.history n))).slot slot).ty) =
 some (.var (GeneralDictionaryHistoricalFields256.representative slot)) :=
 GeneralDictionaryHistoricalFields256.slot_prepared n slot

example (n : Nat) (assignment : Assignment) :
 (GeneralDictionarySlotView256.compact n).Models assignment ↔
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state
   (GeneralPresenceOrderedBlock247.solve model (GeneralDictionaryAggregateHistory256.history n) assignment) :=
 GeneralDictionarySlotView256.compact_solved n assignment

example (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state assignment ∧
   ∀ name, name ≤ 4 → assignment name = boundary name) ↔
 (∃ assignment, (GeneralDictionarySlotView256.compact n).Models assignment ∧
   ∀ name, name ≤ 4 → assignment name = boundary name) := GeneralDictionarySlotView256.public_models n boundary

example (view : GeneralNominalRebaseRawView243.View) (assignment : Assignment) :
 (GeneralDictionaryAggregateRows256.eraseSlotRows view).Models assignment ↔ view.Models assignment :=
 GeneralDictionaryAggregateRows256.slot_rows_irrelevant view assignment

example (n : Nat) : GeneralDictionaryLooseFamilyNames240.lower (n+1) ∈
 GeneralPresenceSubstitutionSupport244.rowSources
   (((GeneralNominalRebaseRawView243.compile (GeneralDictionaryLooseIterationBook240.context (n+1)).state
     (GeneralPresenceOrderedSubstitution247.mapping (GeneralDictionaryAggregateHistory256.history (n+1)))).slot
       (GeneralDictionaryLooseFamilyBase240.anchor (n+1))).row) :=
 GeneralDictionaryAggregateRows256.row_read_retained n

-- Apply the general ordered-elimination bridge to an actually retained source block.
example (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree
   ((GeneralDictionaryAggregateHistory256.history n).map Prod.fst) assignment boundary ∧
   GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state assignment) ↔
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree
   ((GeneralDictionaryAggregateHistory256.history n).map Prod.fst) assignment boundary ∧
   (GeneralNominalRebaseRawView243.compile (GeneralDictionaryLooseIterationBook240.context n).state
     (GeneralPresenceOrderedSubstitution247.mapping (GeneralDictionaryAggregateHistory256.history n))).Models assignment) := by
 apply GeneralNominalOrderedRawPublic256.public_models
 · exact GeneralDictionaryAggregateHistory256.block_in_source n
 · intro entry member
   exact List.mem_map.mpr ⟨entry,member,rfl⟩
