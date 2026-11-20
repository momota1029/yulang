import Yulang.GeneralRebaseDisplayEvidenceWatch284

open Yulang
open GeneralRebaseEpochWindow284 (table run canInstall latestKnown previousKnown)
open GeneralRebaseWindowPorts284 (read Port)
open GeneralRebaseWindowQueries284 (resolve)
open GeneralRebaseWatchValidator284 (update)
open GeneralRebaseWatchBudgetProbe284 (saved cell hole)
open GeneralRebaseFutureCounter284 (future packet present before)
open GeneralRebaseFutureWatch284 (trim)

#eval table.length
#eval (List.range 10).map (fun n => ((run n).later,(run n).phase))
#eval (List.range 10).map (fun n => ((canInstall (run n)), latestKnown (run n), previousKnown (run n)))

def probes : List Port := [⟨.previous,.lower⟩,⟨.latest,.upper⟩,⟨.previous,.upper⟩]
#eval resolve 2 (run 0) probes
#eval resolve 4 (run 4) probes
#eval resolve 2 (run 5) probes
#eval resolve 4 (run 5) probes
#eval read 4 (run 5) ⟨.latest,.lower⟩ == read 4 (run 6) ⟨.previous,.lower⟩
#eval (trim present before).length
#eval ((update ⟨4,present,[]⟩ future packet).isNone)
#eval ((update hole [1,2] []).isNone)
#eval (update (saved 99) (saved 100).watch [cell 100]).map (fun v => (v.watermark,v.kept.length))
#eval (update (saved 99) [100,102] [cell 100]).isNone
