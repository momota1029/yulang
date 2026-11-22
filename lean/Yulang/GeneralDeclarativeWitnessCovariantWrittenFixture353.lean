import Yulang.GeneralDeclarativeWitnessCovariantWrittenState353
import Yulang.GeneralDeclarativeWitnessCovariantIntervalFixture353
import Yulang.GeneralDeclarativeWitnessCovariantNested353

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralDeclarativeWitnessCovariantWrittenFixture353
open GeneralDeclarativeWitnessCovariantWrittenState353 (Line rebuild)
open GeneralDeclarativeWitnessCovariantIntervalFixture353 (problem wire test)
open GeneralDeclarativeWitnessCovariantNested353 (rootProblem data environment report)
open GeneralDeclarativeWitnessCovariantForest353 (Environment decode)

def lines : List Line :=
  [⟨30,.variant 13 (.app 0 [.var 7])⟩,⟨31,.variant 13 (.app 0 [.var 8])⟩,
   ⟨20,.variant 13 (.app 0 [.var 9])⟩]

def intervalLines : List Line :=
  lines ++ [⟨11,.variant 13 (.app 0 [.var 7])⟩,⟨21,.variant 13 (.app 0 [.var 10])⟩]

def testsInterval (ls : List Line) : Bool :=
  ((rebuild problem ls).map (fun p => test p.1 wire)).getD false

theorem roots_reconstructed :
    (rebuild problem intervalLines |>.map (fun a => a.1.rows.map
      (fun (row : GeneralDeclarativeWitnessCovariantOrigin353.Row) => (row.root,row.valueName)))) =
        some [(30,7),(31,8),(20,9),(11,7),(21,10)] := by decide +kernel

theorem written_interval_compiles : testsInterval intervalLines = true := by decide +kernel

theorem missing_written_center :
    testsInterval (intervalLines.eraseIdx 2) = false := by decide +kernel

theorem wrong_written_box :
    testsInterval ([⟨30,.variant 13 (.app 99 [.var 7])⟩] ++ intervalLines.drop 1) = false := by decide +kernel

theorem raw_wrong_kind :
    testsInterval ([⟨30,.variant 13 (.app 0 [.var 7,.var 8])⟩] ++ intervalLines.drop 1) = false := by decide +kernel

def testsForest (ls : List Line) : Bool := (do
  let ⟨actual,_⟩ ← rebuild rootProblem ls
  let (f,s,w) ← data
  let e : Environment actual := ⟨(environment f).origins,(environment f).layout⟩
  pure (decode actual e s w report).isSome) |>.getD false

theorem written_nested_forest_compiles : testsForest lines = true := by decide +kernel

theorem center_cannot_be_reanchored_by_type :
    testsForest (lines.take 2 ++ [⟨99,.variant 13 (.app 0 [.var 9])⟩]) = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantWrittenFixture353
