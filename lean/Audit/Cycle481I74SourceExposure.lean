import Yulang.GeneralDeclarativeI65I74SourceExposure481

namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.Actual
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)

#print axioms exposure_read_reflects_literal_origin
#print axioms literal_origin_reifies_a_checked_exposure
#print axioms every_independent_authored_alias_exposure_has_finite_index_data
#print axioms exposure_trail_replays_the_exact_ordinal_row_sequence
#print axioms exact_exposure_trail_reifies_finite_data
#print axioms every_read_exposure_trail_precomposes_existing_authored_read

def rootRow : Equation := ⟨4,.variant 30 (.variable 6)⟩
def aliasRow : Equation := ⟨6,.variable 7⟩
def fieldRow : Equation := ⟨7,.primitive .emptyRecord []⟩
def before : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,aliasRow,fieldRow]⟩
def authored : Table := ⟨before.equations,[],[]⟩
def pending : Table := ⟨[rootRow,fieldRow],[(aliasRow,9)],[]⟩
def code : Expr := .primitive .emptyRecord []
def pass : ExposureWire := ⟨⟨2,2⟩,[(6,⟨[(6,.same),(7,.forward 1)],⟨[],[]⟩⟩)]⟩
def atPending : ExposureWire := {pass with ordinals := ⟨2,1⟩}

theorem actual_input_exposes_its_authorized_alias_without_changing_old_rows481 :
    readExposure before authored 6 code pass = some fieldRow ∧
    Read (authoredView before authored) .actual (.variable 6) code [] := by
  have picked : readExposure before authored 6 code pass = some fieldRow := by decide +kernel
  exact ⟨picked,one_source_exposure_reads_in_the_same_authored_view picked (.primitive .nil)⟩

theorem no_pending_only_alias_can_supply_this_source_exposure481 (w : ExposureWire) :
    readExposure before pending 6 code w ≠ some fieldRow := by
  intro checked
  have exactAt := exposure_read_reflects_literal_origin _ _ _ _ _ _ checked
  have flat := ObservationRawAlias471.nonidentity_alias_target_is_an_actual_key exactAt.2.2.2
    (by decide : 6 ≠ 7)
  change 7 ∈ ObservationRawAlias471.aliasKeys (authoredView before pending) at flat
  simp [ObservationRawAlias471.aliasKeys,ObservationRawAlias471.boundNames,
    ObservationRawAlias471.onlyFlatKeys,before,pending,rootRow,fieldRow] at flat

/-- info: [true, false, false, false, false, true] -/
#guard_msgs in
#eval [(readExposure before authored 6 code pass).isSome,
  (readExposure before pending 6 code atPending).isSome,
  (readExposure before authored 6 (.variable 22) pass).isSome,
  (readExposure before authored 6 code {pass with ordinals := ⟨2,1⟩}).isSome,
  (readExposure before authored 6 code {pass with aliasData := []}).isSome,
  (readExposureTrail before authored code (.variable 6) [pass]).isSome]

#print axioms actual_input_exposes_its_authorized_alias_without_changing_old_rows481
#print axioms no_pending_only_alias_can_supply_this_source_exposure481
end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.Actual
