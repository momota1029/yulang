import Yulang.GeneralDepthTwoCertifiedRead300

open Yulang
open GeneralDepthTwoFinalNodes300 (Node childNodes code demand)
open GeneralDepthTwoFinalCurrent300 (certificate)
open GeneralNominalVersionedFrame231 (children)

def main : IO Unit := do
  let labels : List Node := [.outer,.inner,.leaf]
  let selected := labels.map (fun n => (certificate n).plan.packet.declaration.id)
  unless selected == [1,1,3] do
    throw (IO.userError "incorrect current declaration")
  let actual := labels.map (fun n => (children (certificate n).plan.packet).map (fun c => c.identity))
  let expect := labels.map (fun n => (childNodes n).map (fun k => (demand k).identity))
  unless actual == expect do
    throw (IO.userError "incorrect current child list")
  IO.println "PASS all three final current effects have the checked IDs and occurrence children"
  IO.println "The proofs distinguish a valid current effect from a novel install; all three effects are already committed."
