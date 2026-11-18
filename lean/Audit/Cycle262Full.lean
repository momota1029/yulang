import Yulang.GeneralFiniteAliasClosure262
import Yulang.GeneralFiniteAliasSearch262
import Yulang.GeneralRebaseExecutableRequests262
import Yulang.GeneralRebaseExecutableSnapshot262
import Yulang.GeneralRebaseRootTrace262
import Yulang.GeneralRebaseAliasRegression262
import Yulang.GeneralRebasePlanTransport262
import Yulang.GeneralRebaseBinderShape262
import Yulang.GeneralRebaseChildRequestPool262
import Yulang.GeneralRebaseSourceRequestPool262
import Yulang.GeneralRebaseDynamicSource262
import Yulang.GeneralRebaseSourceObserver262
import Yulang.GeneralRebaseDynamicTrace262
import Yulang.GeneralRebaseObservedPlan262
import Yulang.GeneralRebasePlanSemantic262
import Yulang.GeneralRebasePlanSemanticExamples262
import Yulang.GeneralRebasePlanTransportExamples262
import Yulang.GeneralRebasePlannedTrace262
import Yulang.GeneralRebaseQuadraticBudget262
import Yulang.GeneralRebaseSelectedCheck262
import Yulang.GeneralRebaseSelectedSettle262
import Yulang.GeneralRebaseSelectedFailure262
import Yulang.GeneralRebaseSelectedMeaning262
import Yulang.GeneralRebaseSelectedRegression262
import Yulang.GeneralRebaseSemanticObserver262
import Yulang.GeneralRebaseSelectedSafety262
import Yulang.GeneralRebaseSelectedUnused262
import Yulang.GeneralRebaseSemanticTrace262
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralFiniteAliasClosure262.", "Yulang.GeneralFiniteAliasSearch262.", "Yulang.GeneralRebaseExecutableRequests262.", "Yulang.GeneralRebaseExecutableSnapshot262.", "Yulang.GeneralRebaseRootTrace262.", "Yulang.GeneralRebaseAliasRegression262.", "Yulang.GeneralRebasePlanTransport262.", "Yulang.GeneralRebaseBinderShape262.", "Yulang.GeneralRebaseChildRequestPool262.", "Yulang.GeneralRebaseSourceRequestPool262.", "Yulang.GeneralRebaseDynamicSource262.", "Yulang.GeneralRebaseSourceObserver262.", "Yulang.GeneralRebaseDynamicTrace262.", "Yulang.GeneralRebaseObservedPlan262.", "Yulang.GeneralRebasePlanSemantic262.", "Yulang.GeneralRebasePlanSemanticExamples262.", "Yulang.GeneralRebasePlanTransportExamples262.", "Yulang.GeneralRebasePlannedTrace262.", "Yulang.GeneralRebaseQuadraticBudget262.", "Yulang.GeneralRebaseSelectedCheck262.", "Yulang.GeneralRebaseSelectedSettle262.", "Yulang.GeneralRebaseSelectedFailure262.", "Yulang.GeneralRebaseSelectedMeaning262.", "Yulang.GeneralRebaseSelectedRegression262.", "Yulang.GeneralRebaseSemanticObserver262.", "Yulang.GeneralRebaseSelectedSafety262.", "Yulang.GeneralRebaseSelectedUnused262.", "Yulang.GeneralRebaseSemanticTrace262."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE262-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
