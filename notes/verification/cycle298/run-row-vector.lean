import Yulang.GeneralRebasePackedRowFixture298
open Yulang
open GeneralRebasePackedAnswers298 (unique pack fill)
open GeneralRebaseQuestionFootprint298 (prior)
open GeneralRebasePackedRowFixture298 (old)
open GeneralRebaseRowChildSource287 (model)
open GeneralNominalCommonBridge (Assignment)

def fallback : Assignment := fun _ => (.top,Common.rowEmpty)
def isNominal (a : Assignment) (n : Nat) : Bool :=
  match (a n).1 with
  | .nominal .. => true
  | _ => false

def main : IO Unit := do
  let scope := prior old
  let original := model Common.rowEmpty
  let boxed := pack scope original
  let restored := fill scope boxed fallback
  unless unique scope.types == [0,1,2] && unique scope.rows == [0] &&
      isNominal original 0 && isNominal restored 0 &&
      isNominal original 1 && isNominal restored 1 &&
      !(isNominal restored 500) do
    throw (IO.userError "row-aware packed fixture diverged")
  IO.println "PASS compiled prior reads type columns [0,1,2] and row column [0] independently."
  IO.println "PASS sparse reconstruction retains the nominal input kinds with a different padded assignment."
  IO.println "The row-sensitive judgment and row-0 necessity are separately proved; this CLI does not decide arbitrary row predicates."
