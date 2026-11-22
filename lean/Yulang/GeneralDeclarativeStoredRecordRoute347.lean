import Yulang.GeneralDeclarativeStoredRecordBase347
import Yulang.GeneralDeclarativeObservedRecordExact347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15400
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeStoredRecordRoute347
open GeneralDeclarativeStoredRecordBase347
open GeneralDeclarativeStoredAuthority347 (Author admits same_input)
open GeneralDeclarativeObservedSyntax347 (rawHead structural)
open GeneralDeclarativeObservedSupport347 (arg)
open GeneralDeclarativeObservedRecord347 (Walk)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeNamedProjection347 (ordinary_holds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEndpointProgram336 (ready Projection Jobs)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeEndpointOverlay336 (receipts spans footprintKeep)
open GeneralDeclarativeEndpointBatch336 (prepare)
open CommonNominalFullCarrier (Equivalent)

abbrev closeEnd : Expr := .primitive .exactEmpty []
abbrev openEnd : Expr := .primitive .emptyRecord []
abbrev loFields : List (Nat × Expr) := [(7,.variable 3)]
abbrev hiFields : List (Nat × Expr) := [(7,.variable 4)]
abbrev loEq : Equation := ⟨0,.record 7 (.variable 3) (.variable 5)⟩
abbrev hiEq : Equation := ⟨2,.record 7 (.variable 4) (.variable 6)⟩
abbrev loEnd : Equation := ⟨5,closeEnd⟩
abbrev hiEnd : Equation := ⟨6,openEnd⟩
abbrev lowRows := [loEq,loEnd]
abbrev highRows := [hiEq,hiEnd]

theorem author_lo : Author raw loEq :=
  ⟨lo,lowTerm,rfl,rfl,rfl,parser_authors lo lowTerm rfl⟩
theorem author_hi : Author raw hiEq :=
  ⟨hi,highTerm,rfl,rfl,rfl,parser_authors hi highTerm rfl⟩
theorem author_lo_end : Author raw loEnd :=
  ⟨lt,.exactEmpty,rfl,rfl,rfl,parser_authors lt .exactEmpty rfl⟩
theorem author_hi_end : Author raw hiEnd :=
  ⟨ht,.emptyRecord,rfl,rfl,rfl,parser_authors ht .emptyRecord rfl⟩

def done (_ : Nat) := False

theorem lower : Walk raw done (admits raw) 0 loFields closeEnd lowRows :=
  .prepend (same_input author_lo) .source
    (.terminal .exactEnd (same_input author_lo_end) .source)

theorem upper : Walk raw done (admits raw) 2 hiFields openEnd highRows :=
  .prepend (same_input author_hi) .source
    (.terminal .width (same_input author_hi_end) .source)

theorem no_center : rawHead raw 1 = none ∧ structural raw 1 = none := by
  have lookup : GeneralDictionaryBinderLocations.sourceSlot raw.base 1 = some mid :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr rfl
  unfold rawHead structural
  rw [lookup]
  exact ⟨rfl,rfl⟩

abbrev cap : Capture := arg site 0
abbrev blank := GeneralDeclarativeNamedProjection347.base raw
def support : Supported blank done := ⟨fun _ _ => False,False.elim⟩
abbrev view := GeneralDeclarativeEntailment320.appendFacts
  (GeneralDeclarativeWherePairView346.extendBounds blank cap) (lowRows++highRows)
abbrev protect : List Nat := [0,1,2,3,4,5,6]
abbrev shape : List (Nat × Nat) := [(7,11)]
abbrev pendingJobs : Jobs :=
  [(11,.field cap 7 (.variable 3) (.variable 4)),(12,.rest cap [7] closeEnd openEnd)]

/-- A checked raw record pair with a genuinely withheld center; four
independent input rows can produce the exact mixed-terminal receipt
list, and they use the real stored center name in the model. -/
theorem same_model_at_inputs :
    ∃ n,
      ModelsExact (prepare view (footprintKeep protect pendingJobs) pendingJobs.length)
        (receipts view (footprintKeep protect pendingJobs) pendingJobs) n ∧
      (spans view (footprintKeep protect pendingJobs) pendingJobs).map Prod.fst = [11,12] ∧
      (∀ k ∈ protect, n k = m k) ∧
      ¬ Equivalent (n 3).1 (n 4).1 ∧ ¬ Equivalent (n 5).1 (n 6).1 := by
  have allowed : shape.map Prod.fst ⊆ (CommonRoleCanonicalRows.normalize loFields).map Prod.fst := by decide +kernel
  have included : shape.map Prod.fst ⊆ (CommonRoleCanonicalRows.normalize hiFields).map Prod.fst := by decide +kernel
  obtain ⟨l,h,jobs,z,read,built,valid,order,kept⟩ :=
    GeneralDeclarativeObservedRecordExact347.materializes support site 0 lower upper shape 12
      (by decide +kernel) allowed included m (stored_site m raw_model) raw_model
      (ordinary_holds _ _ raw_model) protect
  have exactLo : l = loFields := (Option.some.inj read.displayedLow).symm
  have exactHi : h = hiFields := (Option.some.inj read.displayedHigh).symm
  subst l; subst h
  have actual : pendingJobs = jobs := Option.some.inj built
  subst jobs
  have retains (k) (member : k ∈ protect) : z k = m k :=
    kept k (List.mem_append_right _ member)
  refine ⟨z,valid,order,retains,?_,?_⟩
  · rw [retains 3 (by decide +kernel),retains 4 (by decide +kernel)]
    exact CommonNominalFullCarrier.exactEmpty_not_equivalent_width
  · rw [retains 5 (by decide +kernel),retains 6 (by decide +kernel)]
    exact CommonNominalFullCarrier.exactEmpty_not_equivalent_width

end Yulang.GeneralDeclarativeStoredRecordRoute347
