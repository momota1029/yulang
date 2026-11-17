import Yulang.GeneralNominalOrderedPacketModels248
import Yulang.GeneralNominalOrderedLive248
/-! A shared assignment for actual raw state, live sites, packets and consumers.
The lists are explicit inputs, not a claimed enumeration of a whole journal. -/
namespace Yulang.GeneralNominalOrderedBundle248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRebase247 CommonNominalFullCarrier
open GeneralNominalCenters (Site Plan)

theorem sites_exact (sites : List (Site roles)) (entries : List (Entry Nat)) (assignment : Assignment) :
 (∀ site ∈ GeneralNominalRebaseLiveView243.compileAll sites (mapping entries), site.Holds assignment) ↔
 (∀ site ∈ sites, site.Holds (solve model entries assignment)) := by
 simp only [GeneralNominalRebaseLiveView243.compileAll,List.forall_mem_map,
   GeneralNominalRebaseLiveView243.compile_holds,GeneralNominalOrderedRaw248.read_mapping]

theorem public_models_iff (state : GeneralNominalState.State)
 (sites : List (Site roles)) (plans : List (Plan roles)) (old fresh : List (Entry Nat))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Nat)) (sharedNames : Nat → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Assignment) :
 (∃ assignment, GeneralNominalState.Models state assignment ∧
   (∀ site ∈ sites, site.Holds assignment) ∧
   (∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan assignment) ∧
   All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, (GeneralNominalRebaseRawView243.compile state (mapping old)).Models assignment ∧
   (∀ site ∈ GeneralNominalRebaseLiveView243.compileAll sites (mapping old), site.Holds assignment) ∧
   (∀ plan ∈ plans, (GeneralNominalRebasePacketView243.compile plan (mapping old)).Holds assignment) ∧
   All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,raw,live,packets,valid,agree⟩
   have oldValid := ((all_append model assignment _ _).mp valid).2
   obtain ⟨newValid,newPackets⟩ := GeneralNominalOrderedPacketModels248.models_forward
     old fresh oldSafe freshSafe within consumers plans assignment valid packets
   refine ⟨solve model fresh assignment,
     (GeneralNominalOrderedRaw248.raw_forward state old fresh oldSafe within assignment oldValid).mpr raw,
     (GeneralNominalOrderedLive248.sites_forward sites old fresh oldSafe within assignment oldValid).mpr live,
     newPackets,newValid,?_⟩
   intro name shared
   rw [solve_outside model fresh assignment name]
   · exact agree name shared
   · intro entry member
     obtain ⟨original,present,equal⟩ := within entry member
     rw [← equal]
     exact privateTargets name shared original present
 · rintro ⟨assignment,raw,live,packets,valid,agree⟩
   obtain ⟨oldValid,oldPackets⟩ := GeneralNominalOrderedPacketModels248.models_backward
     old fresh oldSafe consumers plans assignment valid packets
   refine ⟨solve model old assignment,
     (GeneralNominalOrderedRaw248.raw_exact state old assignment).mp raw,
     (sites_exact sites old assignment).mp live,oldPackets,oldValid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (privateTargets name shared)]
   exact agree name shared
end Yulang.GeneralNominalOrderedBundle248
