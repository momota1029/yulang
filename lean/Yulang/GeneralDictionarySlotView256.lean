import Yulang.GeneralDictionaryHistoricalFields256
import Yulang.GeneralNominalSlotTypeMap256
import Yulang.GeneralPresenceCommonLaws245
namespace Yulang.GeneralDictionarySlotView256
open Core.PresenceGeneration
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralDictionaryAggregateHistory256 (history)
open GeneralDictionaryHistoricalFields256 (pool representative)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOrderedBlock247 (solve)
open GeneralNominalRebaseRawView243 (View compile)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def expanded (n : Nat) : View := compile (context n).state (mapping (history n))

def compact (n : Nat) : View :=
 GeneralNominalSlotTypeMap256.map (expanded n) (fun slot => .var (representative slot))

theorem compact_exact (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ (expanded n).Models assignment := by
 apply GeneralNominalSlotTypeMap256.models_exact
 intro slot
 exact GeneralPresenceCheckedNormal252.equivalent .lower pool _ _
   (GeneralDictionaryHistoricalFields256.slot_prepared n slot) assignment

/-- Valid projected equations suffice for the old snapshot recovery; source
Models below supplies those equations from the actually retained atoms. -/
theorem recovered (n : Nat) (assignment : Assignment)
 (valid : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history n))) :
 (compact n).Models assignment ↔ GeneralNominalState.Models (context n).state assignment := by
 rw [compact_exact,expanded,GeneralNominalRebaseRawView243.compile_exact]
 have read_eq : GeneralNominalRebaseRawView243.read (mapping (history n)) assignment = solve model (history n) assignment :=
   funext (GeneralPresenceOrderedSubstitution247.mapping_eval (history n) model assignment)
 rw [read_eq]
 exact GeneralNominalRawCongruence238.models_iff _
   (GeneralPresenceOrderedRecovery247.solve_compatible model GeneralPresenceCommonLaws245.common_laws (history n) assignment valid)

theorem source_models (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) :
 (compact n).Models assignment := by
 apply (recovered n assignment (GeneralDictionaryAggregateBasis256.source_history n assignment valid)).mpr
 have raw := valid.1.1
 rw [(GeneralDictionaryLooseIterationIteration240.stages n).shape.current] at raw
 exact raw

theorem slot_values_finite (n : Nat) (slot : Fin (compact n).slots) : ((compact n).slot slot).ty ∈ pool := by
 change TyTerm.var (representative slot) ∈ pool
 have small := GeneralDictionaryHistoricalFields256.representative_small slot
 have cases : representative slot = 0 ∨ representative slot = 1 ∨ representative slot = 2 ∨
   representative slot = 3 ∨ representative slot = 4 := by omega
 rcases cases with equal | equal | equal | equal | equal <;> simp [equal,pool]

theorem slot_count (n : Nat) : (compact n).slots = n+5 := rfl

/-- Only inactive paired metadata is erased, preserving present View.Models.
No old or successor source Step is altered by this representation function. -/
theorem source_erased_rows (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) :
 (GeneralDictionaryAggregateRows256.eraseSlotRows (compact n)).Models assignment :=
 (GeneralDictionaryAggregateRows256.slot_rows_irrelevant (compact n) assignment).mpr (source_models n assignment valid)
/-- Exact interpretation before any equation-validity assumption: expanded
consumers are the original current source read under the ordered solver. -/
theorem compact_solved (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔
 GeneralNominalState.Models (context n).state (solve model (history n) assignment) := by
 rw [compact_exact,expanded,GeneralNominalRebaseRawView243.compile_exact]
 have read_eq : GeneralNominalRebaseRawView243.read (mapping (history n)) assignment = solve model (history n) assignment :=
   funext (GeneralPresenceOrderedSubstitution247.mapping_eval (history n) model assignment)
 rw [read_eq]

theorem solve_initial (n name : Nat) (small : name ≤ 4) (assignment : Assignment) :
 solve model (history n) assignment name = assignment name := by
 apply GeneralPresenceOrderedBlock247.solve_outside
 intro e member
 have above := GeneralDictionaryAggregateHistory256.targets_above n e member
 omega

/-- Current raw-state models, projected to the five fixed initial source
components, are exactly preserved. This is not a journal/packet equivalence. -/
theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralNominalState.Models (context n).state assignment ∧
   ∀ name, name ≤ 4 → assignment name = boundary name) ↔
 (∃ assignment, (compact n).Models assignment ∧
   ∀ name, name ≤ 4 → assignment name = boundary name) := by
 constructor
 · rintro ⟨assignment,valid,agrees⟩
   have blockValid : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history n)) :=
     fun atom member => valid.2.2 atom (GeneralDictionaryAggregateHistory256.block_in_source n member)
   exact ⟨assignment,(recovered n assignment blockValid).mpr valid,agrees⟩
 · rintro ⟨assignment,valid,agrees⟩
   refine ⟨solve model (history n) assignment,(compact_solved n assignment).mp valid,?_⟩
   intro name small
   exact (solve_initial n name small assignment).trans (agrees name small)
end Yulang.GeneralDictionarySlotView256
