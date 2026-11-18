import Yulang.GeneralRebaseMergeFrame261
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMergePacket261
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeStable
open GeneralNominalCenteredHeadAllocMergeConflict (focus chosen current)
open GeneralRebaseMergeRequests261 (candidate packet outputs)

theorem head_schema (atoms) : (candidate atoms).headSchema = ⟨[],[],false⟩ := by
 unfold Plan.headSchema
 simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
   GeneralNominalMaterialization.schemas,
   show chosen.head = [] from rfl]

theorem emissions_empty (identity : Nat) (capture : GeneralDeclarationDemands.Capture)
 (allocate : (clause : GeneralDeclarations.Clause) → GeneralDeclarationDemands.Allocation roles clause) :
 GeneralCanonicalChildOrder.canonicalEmit identity chosen
   GeneralNominalCenteredHeadAllocMergeConflict.chosen_checked capture allocate = [] := by
 apply List.eq_nil_of_length_eq_zero
 rw [GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll_length]
 simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
   show chosen.requirements = [] from rfl]

theorem emitted_schema (atoms) : GeneralNominalVersionedPlans231.emittedSchema (candidate atoms) =
 ⟨[⟨aTarget,.actual,.primitive (.scalar .int) []⟩],false⟩ := by
 unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
 simp only [GeneralRebaseMergeRequests261.packet]
 rw [emissions_empty]
 simp only [List.flatMap_nil,List.append_nil]
 change GeneralNominalCenteredHeadMatSchemas.generated GeneralDeclarationExamples.constructors
   GeneralNominalExamples.interpretation [⟨.app 2 [],aTarget,.actual⟩] = _
 simp [GeneralNominalCenteredHeadMatSchemas.generated,GeneralNominalCenteredHeadMatSchemas.materialize,
   GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_translation,GeneralNominalCenteredHeadMatSchemas.Schema.append]

theorem children_empty (atoms) : GeneralNominalVersionedFrame231.children (packet atoms) = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 simp only [GeneralRebaseMergeRequests261.packet]
 rw [emissions_empty]
 rfl

theorem actual_ready (atoms) : GeneralNominalCenteredHeadMatEffects.Ready (stage atoms).core focus (candidate atoms) := by
 intro output included
 exact (GeneralRebaseBodyTable261.translated (candidate atoms) output).mp
   (GeneralRebaseMergeRequests261.ready atoms output ((GeneralRebaseMergeRequests261.requests_exact atoms output).mp included))

theorem packet_holds (atoms) (assignment : Assignment)
 (raw : GeneralNominalState.Models (current atoms).state assignment)
 (effects : GeneralRebaseClassTable261.Effects (candidate atoms) outputs assignment) :
 GeneralNominalVersionedPlans231.Holds (candidate atoms) assignment := by
 refine ⟨raw,⟨GeneralRebaseMergeFrame261.ordinary atoms assignment,
   (GeneralRebaseMergeFrame261.head_models atoms assignment raw).2,?_,?_,?_,?_,?_⟩,?_⟩
 · intro index; exact Fin.elim0 index
 · intro name needed
   rcases needed with member | needed
   · cases member
   · obtain ⟨clause,member,_⟩ := needed
     cases member
 · rw [head_schema]
   constructor
   · intro test member; cases member
   · intro entry member; cases member
 · rw [emitted_schema]
   intro equation member notActual
   cases List.mem_singleton.mp member
   exact False.elim (notActual rfl)
 · intro clause member
   cases member
 · unfold GeneralNominalVersionedPlans231.Outputs
   rw [emitted_schema]
   intro equation member
   cases List.mem_singleton.mp member
   exact ((GeneralRebaseMergeMeaning261.effects_exact atoms assignment).mp effects).1

theorem evidence (atoms) (good : Good atoms) (supported : Supported atoms) (assignment : Assignment)
 (raw : GeneralNominalState.Models (current atoms).state assignment)
 (effects : GeneralRebaseClassTable261.Effects (candidate atoms) outputs assignment) :
 GeneralNominalVersionedEvidence231.Evidence registry (stage atoms).core assignment focus (.node 38 []) := by
 apply GeneralNominalVersionedEvidence231.evidence_leaf
 refine ⟨candidate atoms,?_⟩
 exact GeneralNominalVersionedEvidence231.certificate_of_semantics
   (GeneralRebaseMergeFrame261.frame atoms good supported) (children_empty atoms).symm
   (packet_holds atoms assignment raw effects) (actual_ready atoms)
   ((GeneralRebaseMergeRequests261.effects_exact atoms assignment).mp effects)

/-- This raw-only evidence deliberately does not claim a journal/history model.
The history-preserving finite state is uninhabited on this reached fixture. -/
theorem raw_only_evidence (atoms) (good : Good atoms) (supported : Supported atoms) :
 GeneralNominalVersionedEvidence231.Evidence registry (stage atoms).core uniform focus (.node 38 []) :=
 evidence atoms good supported uniform (raw_uniform good) (GeneralRebaseMergeMeaning261.uniform_effects atoms)
end Yulang.GeneralRebaseMergePacket261
