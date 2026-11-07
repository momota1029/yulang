import Yulang.CommonBoundRefSolver
open Yulang Yulang.Core.PresenceGeneration
open Yulang.CommonPresenceConstraintGraph
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
#eval (CommonBoundRefSolver.solveAll (compile ([.tyLe (.variant 0 (.base .int)) (.variant 0 (.base .int))] : List (PresenceNormalForm.Atom (Fin 0))))).length
#eval (CommonBoundRefSolver.solveAll (compile ([.tyLe (.var 0) (.variant 0 (.base .int))] : List (PresenceNormalForm.Atom (Fin 1))))).length
