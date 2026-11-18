import Yulang.GeneralDictionaryUniformJournal258
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
end Yulang
