import Yulang.GeneralDeclarativeI65I74SourceExposure481

namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.DistinctAuthoredPaths
open GeneralDeclarativeHead320 (Equation environment Models)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

def code : Expr := .primitive .emptyRecord []
def eqA : Equation := ⟨6,.variable 7⟩
def eqB : Equation := ⟨6,.variable 8⟩
def ownA : Equation := ⟨7,code⟩
def ownB : Equation := ⟨8,code⟩
def eqs : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[eqA,eqB,ownA,ownB]⟩
def phase : Table := ⟨eqs.equations,[],[]⟩
def allKnown : ObservationAliasHead472.Catalogue :=
  [(6,⟨[(6,.same),(7,.forward 0),(8,.forward 1)],⟨[],[]⟩⟩)]
def wA : ExposureWire := ⟨⟨2,2⟩,allKnown⟩
def wB : ExposureWire := ⟨⟨3,3⟩,allKnown⟩

def valueModel : Assignment := fun _ => (.emptyRecord,Common.rowEmpty)

theorem same_ordinary_snapshot_is_inhabited481 : Models eqs valueModel := by
  refine ⟨⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro row occurrence
  change row ∈ [eqA,eqB,ownA,ownB] at occurrence
  simp only [List.mem_cons,List.not_mem_nil,or_false] at occurrence
  rcases occurrence with rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem independent_occurrence_data_select_distinct_alias_owners481 :
    readExposure eqs phase 6 code wA = some ownA ∧
    readExposure eqs phase 6 code wB = some ownB ∧
    Read (authoredView eqs phase) .actual
      (.primitive .pair [.variable 6,.variable 6]) (.primitive .pair [code,code]) [] := by
  have first : readExposure eqs phase 6 code wA = some ownA := by decide +kernel
  have second : readExposure eqs phase 6 code wB = some ownB := by decide +kernel
  refine ⟨first,second,?_⟩
  exact .primitive (.cons
    (one_source_exposure_reads_in_the_same_authored_view first (.primitive .nil))
    (.cons (one_source_exposure_reads_in_the_same_authored_view second (.primitive .nil)) .nil))

theorem one_global_alias_redirect_cannot_encode_these_two_positions481 :
    ¬∃ redirect : Nat → Nat, redirect 6 = ownA.left ∧ redirect 6 = ownB.left := by
  rintro ⟨redirect,a,b⟩
  have eq := a.symm.trans b
  contradiction

#print axioms same_ordinary_snapshot_is_inhabited481
#print axioms independent_occurrence_data_select_distinct_alias_owners481
#print axioms one_global_alias_redirect_cannot_encode_these_two_positions481
end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.DistinctAuthoredPaths
