import Yulang.GeneralDeclarativeRecordHead323
import Yulang.GeneralDeclarativeClauseOrigins325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordProducer325
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeRecordWalk323 (substFields)
open GeneralDeclarativeRecordResidual323 (withTail reconstruct_with_terminal permute_fields)
open GeneralDeclarativeRecordHead323 (FieldValue field_congr logical_spine selected_nodup)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDeclarationPatterns (normalize)
open CommonRoleCanonicalRows (Row selected residual)
open CommonRoleOutermostResolver (All₂)

def FieldDerives (s : State) (actual code : Nat × Expr) : Prop :=
  actual.1 = code.1 ∧ Derives s actual.2 code.2

theorem field_values {s : State} (rows : All₂ (FieldDerives s) actual normal) (m) (valid : Models s m) :
    All₂ (FieldValue m) actual normal := by
  induction rows with
  | nil => exact .nil
  | cons one rest ih => exact .cons ⟨one.1,semantic one.2 m valid⟩ ih

/-- Once a concrete canonical spine has been observed, the record tail
is the source's actual computed subtraction, at an ordinary declared
logical name. Exact-ended records, unlike arbitrary open tails, can
supply the relevant evidence. No raw spelling needs interpretation. -/
theorem normalized_tail {s : State} {cap : Nat → Capture}
    (unique : (actual.map Prod.fst).Nodup)
    (normal : translate c i (normalize p) = some (withTail written (.variable binder)))
    (center : Origin s arg.center (withTail actual terminal))
    (tail : Origin s (cap binder).center (withTail (residual (written.map Prod.fst) actual) terminal))
    (ordered : (selected (written.map Prod.fst) actual).Perm inSourceOrder)
    (fields : All₂ (FieldDerives s) inSourceOrder (substFields cap .actual written)) :
    Result s (fact c i cap arg p) := by
  refine ⟨[⟨arg.center,logical cap .actual (withTail written (.variable binder))⟩],
    by simp [fact,normal],?_⟩
  intro row there m valid
  cases List.mem_singleton.mp there
  have split : eqAt m (withTail actual terminal) (logical cap .actual (withTail written (.variable binder))) := by
    rw [logical_spine]
    exact eqv_trans (reconstruct_with_terminal m actual _ terminal unique)
      (eqv_trans (permute_fields m _ ordered (selected_nodup actual _ unique))
        (field_congr m (field_values fields m valid) (eqv_symm (entails (origin_reads tail) m valid))))
  exact eqv_trans (entails (origin_reads center) m valid) split

end Yulang.GeneralDeclarativeRecordProducer325
