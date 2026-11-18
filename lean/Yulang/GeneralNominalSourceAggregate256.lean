import Yulang.GeneralNominalAggregateAtoms256
import Yulang.GeneralNominalCanonicalBasis255
import Yulang.GeneralNominalAllocationSupport
namespace Yulang.GeneralNominalSourceAggregate256
open Core.PresenceGeneration GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocation GeneralNominalRecursiveInspection
open GeneralPresenceCheckedNormal252
open GeneralNominalAggregateAtoms256

/-- The fixed source/public basis already contains each initial endpoint. -/
theorem source_variable (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (name : Nat) (member : name ∈ GeneralNominalState.sources context.state) :
 TyTerm.var name ∈ GeneralNominalCanonicalBasis255.basis registry context keys := by
 apply List.mem_eraseDups.mpr
 apply List.mem_append_right
 exact List.mem_map.mpr ⟨name,List.mem_append_left _ member,rfl⟩

theorem report_lower (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (declaration : Declaration)
 (bounds : List (GeneralNominalInspection.Bounds context.state))
 (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds))
 (name : Nat) (named : name ∈ declaration.inputNames) :
 atoms .lower ((lower (occurrences (bindings context.state
   (GeneralNominalRecursiveCandidates.report context declaration bounds)) name)).subst CompTerm.var) ⊆
 GeneralNominalCanonicalBasis255.basis registry context keys := by
 apply (lower_supported_iff _ (GeneralNominalInputOccurrences256.report_nonempty context declaration bounds finished name named) _ _).mpr
 intro pair member atom present
 cases List.mem_singleton.mp present
 exact source_variable registry context keys _
   (GeneralNominalAllocationSupport.occurrences_endpoints
     (GeneralNominalAllocationSupport.report_endpoints context.state _) name pair member).1

theorem report_upper (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (declaration : Declaration)
 (bounds : List (GeneralNominalInspection.Bounds context.state))
 (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds))
 (name : Nat) (named : name ∈ declaration.inputNames) :
 atoms .upper ((upper (occurrences (bindings context.state
   (GeneralNominalRecursiveCandidates.report context declaration bounds)) name)).subst CompTerm.var) ⊆
 GeneralNominalCanonicalBasis255.basis registry context keys := by
 apply (upper_supported_iff _ (GeneralNominalInputOccurrences256.report_nonempty context declaration bounds finished name named) _ _).mpr
 intro pair member atom present
 cases List.mem_singleton.mp present
 exact source_variable registry context keys _
   (GeneralNominalAllocationSupport.occurrences_endpoints
     (GeneralNominalAllocationSupport.report_endpoints context.state _) name pair member).2

/-- Both checks succeed in the identity snapshot of the given source context.
This is not a claim about the historical mapping at every later state. -/
theorem report_prepared (registry : Registry) (context : GeneralNominalCandidates.Context)
 (keys : List (Nat × Nat)) (declaration : Declaration)
 (bounds : List (GeneralNominalInspection.Bounds context.state))
 (finished : Finished (GeneralNominalRecursiveCandidates.report context declaration bounds))
 (name : Nat) (named : name ∈ declaration.inputNames) :
 let pairs := occurrences (bindings context.state (GeneralNominalRecursiveCandidates.report context declaration bounds)) name
 let pool := GeneralNominalCanonicalBasis255.basis registry context keys
 prepare .lower pool ((lower pairs).subst CompTerm.var) = some (normalize .lower pool ((lower pairs).subst CompTerm.var)) ∧
 prepare .upper pool ((upper pairs).subst CompTerm.var) = some (normalize .upper pool ((upper pairs).subst CompTerm.var)) :=
 ⟨(prepare_exact ..).mpr ⟨report_lower registry context keys declaration bounds finished name named,rfl⟩,
  (prepare_exact ..).mpr ⟨report_upper registry context keys declaration bounds finished name named,rfl⟩⟩

theorem frame_prepared
 (frame : GeneralNominalVersionedEvidence231.Frame registry state root key plan)
 (keys : List (Nat × Nat)) (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
 let pairs := occurrences (bindings plan.packet.context.state
   (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds)) name
 let pool := GeneralNominalCanonicalBasis255.basis registry plan.packet.context keys
 prepare .lower pool ((lower pairs).subst CompTerm.var) = some (normalize .lower pool ((lower pairs).subst CompTerm.var)) ∧
 prepare .upper pool ((upper pairs).subst CompTerm.var) = some (normalize .upper pool ((upper pairs).subst CompTerm.var)) :=
 report_prepared registry plan.packet.context keys plan.packet.declaration plan.packet.bounds
   (GeneralNominalInputOccurrences256.frame_finished frame) name named
end Yulang.GeneralNominalSourceAggregate256
