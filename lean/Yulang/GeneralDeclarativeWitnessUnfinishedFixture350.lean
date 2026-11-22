import Yulang.GeneralDeclarativeWitnessUnfinished350
import Yulang.GeneralDeclarativeWitnessCycleFixture350
import Yulang.GeneralDeclarativeWitnessRecordLeafFixture350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessUnfinishedFixture350
open GeneralDeclarativeWitnessCycleFixture350 (state shape d certificate)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeWitnessUnfinished350 (Wire check checkResult checked)
open GeneralDeclarativeWitnessProblem349 (Problem)
open GeneralDeclarativeWitnessTree349 (Report)

def provenance : Table := ⟨[],[(shape,9)],[]⟩
def wire : Wire := ⟨certificate,0,.forward 0,[]⟩

theorem independently_unfinished : check state provenance d wire = true := by decide +kernel

theorem promoted_is_not_pending :
    check state {provenance with released := [9]} d wire = false := by decide +kernel

theorem authorized_same_root_head :
    check state {provenance with authored := [shape]} d wire = false := by decide +kernel

theorem wrong_pending_owner_route :
    check state provenance d {wire with ownerAlias := .same} = false := by decide +kernel

theorem no_author_row :
    check state {provenance with produced := []} d wire = false := by decide +kernel

abbrev exampleProblem : Problem :=
  ⟨GeneralDeclarativeWitnessRecordLeafFixture350.input,state,d⟩

def actualReport : Report := ⟨.rejected,.rejected,[]⟩

theorem literal_rejected : checkResult exampleProblem provenance wire actualReport = true := by decide +kernel

theorem cannot_call_it_pending :
    checkResult exampleProblem provenance wire ⟨.pending,.pending,[]⟩ = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessUnfinishedFixture350
