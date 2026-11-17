import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralPresenceOrderedRebase247
/-! Full actual raw nominal-state model transport through ordered expressions.
The raw source field, heads and descriptor endpoints are compiled, not hidden.
A successor operational state and separate packet/history/cache fields remain
outside this theorem; all listed requirements share one assignment witness. -/
namespace Yulang.GeneralNominalOrderedRaw248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open CommonNominalFullCarrier

theorem read_mapping (entries : List (Entry Nat)) (assignment : Assignment) :
 GeneralNominalRebaseRawView243.read (mapping entries) assignment = solve model entries assignment :=
 funext (mapping_eval entries model assignment)

theorem raw_exact (state : GeneralNominalState.State) (entries : List (Entry Nat)) (assignment : Assignment) :
 (GeneralNominalRebaseRawView243.compile state (mapping entries)).Models assignment ↔
 GeneralNominalState.Models state (solve model entries assignment) := by
 rw [GeneralNominalRebaseRawView243.compile_exact,read_mapping]

theorem raw_forward (state : GeneralNominalState.State) (old fresh : List (Entry Nat))
 (safe : SafeOrder old) (within : TargetsWithin fresh old) (assignment : Assignment)
 (valid : All model assignment (block old)) :
 (GeneralNominalRebaseRawView243.compile state (mapping old)).Models (solve model fresh assignment) ↔
 GeneralNominalState.Models state assignment := by
 rw [raw_exact,solve_absorbs model old fresh safe within]
 exact GeneralNominalRawCongruence238.models_iff state
   (GeneralPresenceOrderedRecovery247.solve_compatible model GeneralPresenceCommonLaws245.common_laws old assignment valid)

theorem raw_public_models_iff (state : GeneralNominalState.State) (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Nat)) (sharedNames : Nat → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalState.Models state assignment ∧
   All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseRawView243.compile state (mapping old)).Models assignment ∧
   All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,raw,valid,agree⟩
   refine ⟨solve model fresh assignment,?_,models_forward model GeneralPresenceCommonLaws245.common_laws old fresh oldSafe freshSafe within consumers assignment valid,?_⟩
   · exact (raw_forward state old fresh oldSafe within assignment
       ((all_append model assignment consumers (block old)).mp valid).2).mpr raw
   · intro name shared
     rw [solve_outside model fresh assignment name]
     · exact agree name shared
     · intro entry member
       obtain ⟨original,present,equal⟩ := within entry member
       rw [← equal]
       exact privateTargets name shared original present
 · rintro ⟨assignment,raw,valid,agree⟩
   refine ⟨solve model old assignment,(raw_exact state old assignment).mp raw,
     models_backward model GeneralPresenceCommonLaws245.common_laws old fresh oldSafe consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (privateTargets name shared)]
   exact agree name shared
end Yulang.GeneralNominalOrderedRaw248
