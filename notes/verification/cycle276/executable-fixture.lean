import Yulang.GeneralRebaseDisplayPayload276
open Yulang
#eval (GeneralRebaseDisplayExecutor276.run 1).isSome
#eval (GeneralRebaseDisplayExecutor276.run 3).isNone
#eval (GeneralRebaseDisplayExecutor276.emit 1 .parent).isNone
#eval GeneralRebaseDisplayPayload276.accepts .parent (.node 1 [.node 3 []])
#eval GeneralRebaseDisplayPayload276.accepts .parent (.node 1 [])
#eval GeneralRebaseDisplayPayload276.accepts .parent (.node 1 [.node 3 [], .node 3 []])
#eval GeneralRebaseDisplayPayload276.accepts .child (.node 3 [])
