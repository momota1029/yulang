import Yulang.GeneralDictionaryFiniteJournal257
namespace Yulang
open CommonNominalFullCarrier
example : ¬ GeneralDictionaryBinderFact257.Holds GeneralDictionaryBinderGap257.seed := by
 intro binder
 have transported := (GeneralDictionaryFiniteJournal257.solve_binder 1 GeneralDictionaryBinderGap257.seed).mpr binder
 exact GeneralDictionaryBinderFact257.excludes_gap 0 transported

/-- The positive-stage qualifier cannot be dropped, even at the initial model. -/
example : GeneralNominalVersionedJournal232.Models GeneralDictionaryLooseLoopSource240.initial
 GeneralDictionaryBinderGap257.seed ∧
 ¬ (GeneralDictionaryFiniteJournal257.view 0).Models GeneralDictionaryBinderGap257.seed := by
 refine ⟨GeneralDictionaryBinderGap257.seed_models,?_⟩
 intro small
 have binder := (GeneralDictionaryFiniteJournal257.models_exact 0 GeneralDictionaryBinderGap257.seed).mp small |>.2
 have transported := (GeneralDictionaryFiniteJournal257.solve_binder 1 GeneralDictionaryBinderGap257.seed).mpr binder
 exact GeneralDictionaryBinderFact257.excludes_gap 0 transported
end Yulang
