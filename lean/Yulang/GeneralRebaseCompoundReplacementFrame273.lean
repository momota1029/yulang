import Yulang.GeneralRebaseCompoundReplacement273
import Yulang.GeneralNominalVersionedEffectCongruence238

set_option maxRecDepth 26000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompoundReplacementFrame273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralDictionaryCompoundPoint238 (point allocated reserved ordinary)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralDictionaryCompoundSource238 (child declaration registry)
open GeneralDictionaryJournalRefinement228Source (root snapshot)
open GeneralDictionaryJournalRefinement228Reobserve (pointExtended looseExtended extended_models_iff)
open GeneralNominalVersionedPlans231 (Holds HeadModels Ordinary private_models_iff emittedSchema variables childSchema Outputs)
open GeneralRebaseTypeOnlyAtoms273 (atomTypeOnly all_iff)
open GeneralRebaseRowIrrelevance273 (SameTypes)
open GeneralRebaseCompoundReplacement273 (patch emitted_same)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralNominalVersionedEffects231 (ClassEffects)

def Meaning (model : Assignment) : Prop :=
 Holds currentPlan model ∧ ClassEffects point.core root currentPlan model

theorem canonical_valid : Meaning (patch extended) :=
 ⟨GeneralRebaseCompoundReplacement273.holds,GeneralRebaseCompoundReplacement273.class_holds⟩

theorem snapshot_exact (m : Assignment) :
 GeneralNominalState.Models currentPlan.packet.context.state m ↔
 GeneralNominalState.Models snapshot m ∧ PresenceNormalForm.All CommonNominalFullCarrier.model m ordinary := by
 exact (extended_models_iff allocated reserved ordinary m).trans (by
   constructor
   · intro m; exact ⟨⟨m.1,m.2.1,PresenceNormalForm.all_nil _ _⟩,m.2.2⟩
   · rintro ⟨m,a⟩; exact ⟨m.1,m.2.1,a⟩)

theorem old_atoms_type_only : ordinary.all atomTypeOnly = true := by decide +kernel

noncomputable abbrev packet := currentPlan.packet

noncomputable def merges := GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry
 packet.site.occurrence.identity packet.declaration packet.bindings

noncomputable def checks := GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet)

theorem merges_type_only : merges.all atomTypeOnly = true := by decide +kernel
theorem checks_type_only : checks.all atomTypeOnly = true := by decide +kernel

theorem current_ordinary (same : SameTypes first last) : Ordinary packet first ↔ Ordinary packet last := by
 unfold Ordinary
 apply and_congr ?_ (and_congr (all_iff same merges merges_type_only) (all_iff same checks checks_type_only))
 unfold GeneralNominalAllocation.Compatible
 exact forall_congr' fun a => forall_congr' fun _ => forall_congr' fun b => forall_congr' fun _ =>
   forall_congr' fun _ => by rw [same a.2.1,same b.2.2]

theorem current_source (same : SameTypes first last) :
 GeneralNominalState.Models packet.context.state first ↔ GeneralNominalState.Models packet.context.state last := by
 rw [snapshot_exact,snapshot_exact]
 exact and_congr (GeneralRebaseCompoundRows273.source same) (all_iff same ordinary old_atoms_type_only)

theorem head_row_free (same : SameTypes first last) :
 HeadModels packet first ↔ HeadModels packet last := by
 unfold HeadModels
 rw [private_models_iff,private_models_iff]
 exact and_congr (and_congr (current_source same) (current_ordinary same))
   (GeneralRebaseRowIrrelevance273.projection same _ _)

theorem holds_row_free (same : SameTypes first last) :
 Holds currentPlan first ↔ Holds currentPlan last := by
 rw [GeneralNominalVersionedPacketFrame236.holds_shape,GeneralNominalVersionedPacketFrame236.holds_shape]
 apply and_congr (head_row_free same)
 apply and_congr (GeneralRebaseRowIrrelevance273.site same currentPlan.input)
 apply and_congr
 · exact forall_congr' fun n => forall_congr' fun _ => by
     rw [same (GeneralNominalVersionedFrame231.binder currentPlan n)]
     exact GeneralRebaseRowIrrelevance273.capture same _ _
 apply and_congr (GeneralRebaseRowIrrelevance273.head_schema same currentPlan currentPlan.headSchema)
 apply and_congr
 · exact forall_congr' fun eq => forall_congr' fun _ => forall_congr' fun _ =>
     GeneralRebaseRowIrrelevance273.equation same currentPlan eq
 apply and_congr
 · exact forall_congr' fun clause => forall_congr' fun _ => forall_congr' fun valid =>
     and_congr (GeneralRebaseRowIrrelevance273.site same _) (GeneralRebaseRowIrrelevance273.schema same currentPlan (childSchema currentPlan clause valid))
 · exact GeneralRebaseRowIrrelevance273.schema same currentPlan (emittedSchema currentPlan)

theorem meaning_row_free (same : SameTypes first last) :
 Meaning first ↔ Meaning last :=
 and_congr (holds_row_free same) (GeneralRebaseRowIrrelevance273.live same point.core root currentPlan)

theorem meaning_equivalent (same : GeneralNominalAssignmentCongruence238.Same first last) :
 Meaning first ↔ Meaning last :=
 and_congr (GeneralNominalVersionedPacketCongruence238.holds_iff same currentPlan)
   (GeneralNominalVersionedEffectCongruence238.class_iff same point.core root currentPlan)

theorem output_necessary (m : Assignment) (valid : Holds currentPlan m) : Body m := by
 have out := valid.2.2
 unfold Outputs at out
 rw [emitted_same,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema] at out
 exact out _ List.mem_cons_self

theorem fixed_of_meaning (m : Assignment) (valid : Meaning m) : Fixed m :=
 (GeneralRebaseCompoundSourceTypes273.restricted_exact m).mpr
  ⟨GeneralRebaseCompoundSourceTypes273.source_reads m ((snapshot_exact m).mp valid.1.1).1,
   output_necessary m valid.1⟩

end Yulang.GeneralRebaseCompoundReplacementFrame273
