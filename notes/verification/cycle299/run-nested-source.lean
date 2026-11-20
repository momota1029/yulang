import Yulang.GeneralGeneratedNestedInstallInterface299

open Yulang
open GeneralGeneratedNestedSource299 (root)
open GeneralGeneratedNestedPredictions299 (middle terminal parentPacket middlePacket terminalPacket)
open GeneralNominalVersionedFrame231 (children)

def main : IO Unit := do
  unless (children parentPacket).length == 1 && (children middlePacket).length == 1 &&
      (children terminalPacket).isEmpty do
    throw (IO.userError "unexpected where shape")
  unless middle.demand.arguments ⟨0,by decide +kernel⟩ == (1,1) &&
      terminal.demand.arguments ⟨0,by decide +kernel⟩ == (2,2) do
    throw (IO.userError "incorrect nested demand input")
  unless root.identity != middle.identity && middle.identity != terminal.identity do
    throw (IO.userError "child identity collision")
  IO.println "PASS grounded V8 input has the predicted nominal where descent slot 0 → slot 1 → slot 2"
  IO.println "PASS preliminary packets emit one distinct child each, then a terminal leaf"
  IO.println "Packet prediction only: no new raw install or post-install evidence is executed by this check."
