import Yulang.GeneralDictionaryPrivateBoundary258
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
end Yulang
