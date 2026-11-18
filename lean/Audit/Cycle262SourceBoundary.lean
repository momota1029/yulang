import Yulang.GeneralRebaseSourceRequestPool262
import Yulang.GeneralDictionaryVersionLoopNontermination239
import Yulang.GeneralDictionaryMixedDefault202234

open Yulang
namespace Cycle262SourceBoundary
open GeneralDictionaryVersionLoopSource237

/-- A finite request pool does not establish accessibility of the old Step.
The same genuine source has both properties, so no simulation is implicit. -/
theorem finite_pool_with_old_loop :
 (∃ pool : List GeneralSourceState.Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root)
   initial state → GeneralRebaseChildRequestPool262.Covered state.core pool) ∧
 ¬ Acc GeneralDictionaryVersionLoopNontermination239.reverseStep initial :=
 ⟨GeneralRebaseSourceRequestPool262.mixed_finite_requests sourceRegistry root initial
   GeneralDictionaryVersionLoopInitial238.initial_source,
   GeneralDictionaryVersionLoopNontermination239.initial_no_acc⟩

end Cycle262SourceBoundary
#print axioms Cycle262SourceBoundary.finite_pool_with_old_loop

namespace Cycle262DefaultSource
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryVersionedDefault202233

theorem covered : ∃ pool : List GeneralSourceState.Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root)
   current state → GeneralRebaseChildRequestPool262.Covered state.core pool :=
 GeneralRebaseSourceRequestPool262.mixed_finite_requests registry root current
   GeneralDictionaryMixedDefault202234.initial
end Cycle262DefaultSource
#print axioms Cycle262DefaultSource.covered
