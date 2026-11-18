import Yulang.GeneralDictionaryCompletedReadback258
namespace Yulang
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryUniformFill258 (fill)
example (a : Assignment) : fill (fill a) = fill a := GeneralDictionaryUniformFill258.idempotent a
example (a : Assignment) : GeneralDictionaryFiniteJournal257.Agree (fill a) a := GeneralDictionaryUniformFill258.agrees a
example (a : Assignment) (n : Nat) : PresenceNormalForm.All CommonNominalFullCarrier.model (fill a)
 (GeneralPresenceDefinitionRewrite244.block (GeneralDictionaryUpperHistory257.history n)) :=
 GeneralDictionaryUniformBlock258.all_blocks a n
example (a : Assignment) : (∀ n, GeneralNominalVersionedJournal232.Models
 (GeneralDictionaryLooseIterationIteration240.state n) (fill a)) ↔
 (GeneralDictionaryFiniteJournal257.view 1).Models a := GeneralDictionaryUniformJournal258.all_stages a
example (boundary : Assignment) :
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧ ∀ n,
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) a) ↔
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧ (GeneralDictionaryFiniteJournal257.view 1).Models a) :=
 GeneralDictionaryUniformJournal258.simultaneous_models boundary
example (n : Nat) (boundary : Assignment) :
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) a) ↔
 (∃ a, GeneralDictionaryFiniteJournal257.Agree a boundary ∧ ∀ index,
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state index) a) :=
 GeneralDictionaryUniformJournal258.positive_models n boundary
example (a : Assignment) :
 (∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n)
   (GeneralDictionaryInitialFill258.complete a)) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot a := GeneralDictionaryInitialFill258.all_stages a
example (boundary : Assignment) :
 (∃ a, GeneralDictionaryInitialProjection257.Agree a boundary ∧ ∀ n,
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) a) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary :=
 GeneralDictionarySourceExtension258.simultaneous_models boundary
example (n : Nat) : ¬ ∃ a, GeneralDictionaryFiniteJournal257.Agree a GeneralDictionaryBinderGap257.seed ∧
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) a :=
 GeneralDictionaryPrivateBoundary258.retained_binder_impossible n
example : GeneralDictionaryInitialFill258.complete GeneralDictionaryBinderGap257.seed ≠ GeneralDictionaryBinderGap257.seed :=
 GeneralDictionaryPrivateBoundary258.changes_seed
example (n : Nat) : (GeneralDictionaryDirectView258.view n).ordinary.length = 4+16*n :=
 GeneralDictionaryDirectView258.ordinary_length n
example (name : Nat) : GeneralDictionaryFastFill258.lower name = GeneralDictionaryFamilyRecognition258.isLower name :=
 GeneralDictionaryFastFill258.lower_exact name
example (a : Assignment) : GeneralDictionaryFastFill258.complete a = GeneralDictionaryInitialFill258.complete a :=
 GeneralDictionaryFastFill258.complete_exact a
example (a : Assignment) :
 (∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n)
   (GeneralDictionaryFastFill258.complete a)) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot a := GeneralDictionaryFastFill258.all_stages a
example (index : Nat) : GeneralDictionarySearchCost258.probes
 (fun i => GeneralDictionaryLooseFamilyNames240.lower (i+1)) (GeneralDictionaryLooseFamilyNames240.lower (index+1))
 0 (GeneralDictionaryLooseFamilyNames240.lower (index+1)+1) ≤ index+1 := GeneralDictionarySearchCost258.lower_match index
example (a : Assignment) :
 GeneralNominalVersionedPlans231.Holds GeneralDictionaryOutputDepth252.plan
 (GeneralDictionaryOutputFrame258.complete a) ↔
 GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot a := GeneralDictionaryOutputCompletion258.packet_exact a
example (a : Assignment) (valid : GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot a) :
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed
 (GeneralDictionaryOutputFrame258.complete a) := GeneralDictionaryOutputCompletion258.installed_models a valid
example (payload : GeneralDictionaryReadback.Payload) :
 ¬ GeneralNominalVersionedEvidence231.Evidence GeneralDictionaryOutputDepth252.registry GeneralDictionaryOutputDepth252.initial.core
 (GeneralDictionaryPendingOutput258.replace .bottom) GeneralDictionaryOutputDepth252.root payload :=
 GeneralDictionaryOutputEvidence258.no_initial_evidence payload
example (a : Assignment) (valid : GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot a) :
 GeneralNominalVersionedEvidence231.Evidence GeneralDictionaryOutputDepth252.registry GeneralDictionaryOutputDepth252.initial.core
 (GeneralDictionaryOutputFrame258.complete a) GeneralDictionaryOutputDepth252.root (.node 0 []) :=
 GeneralDictionaryOutputEvidence258.completed_evidence a valid
example (boundary : Assignment) :
 (∃ a, GeneralDictionaryOutputPublic258.Agree a boundary ∧
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed a) ↔
 GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot boundary := GeneralDictionaryOutputPublic258.public_models boundary
example : GeneralPatternAdditiveDepth253.depth GeneralDictionaryOutputDepth252.expanded = 4 :=
 GeneralDictionaryCompletedReadback258.depth
end Yulang
