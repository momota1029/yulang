import Yulang.GeneralRebaseOutputKeys260
import Yulang.GeneralRebaseOutputDecoder260
import Yulang.GeneralOutputRebaseSource260
import Yulang.GeneralOutputRebaseModels260
import Yulang.GeneralOutputRebaseInstalled260
import Yulang.GeneralOutputRebaseRun260
import Yulang.GeneralOutputRebasePublic260
import Yulang.GeneralRebaseOwnedOutputKeys260
import Yulang.GeneralRebaseOutputFamily260
import Yulang.GeneralRebaseOutputFamilyRun260
import Yulang.GeneralOwnedOutputDecoder260
import Yulang.GeneralOwnedOutputActual260
import Yulang.GeneralDefaultRebaseBody260
import Yulang.GeneralDefaultRebaseSource260
import Yulang.GeneralDefaultRebaseModels260
import Yulang.GeneralDefaultRebaseInstalled260
import Yulang.GeneralDefaultRebaseRun260
import Yulang.GeneralDefaultRebaseCompletion260
import Yulang.GeneralDefaultRebasePublic260
import Yulang.GeneralRebaseBodyDecoder260
import Yulang.GeneralReflexiveDefaultSource260
import Yulang.GeneralReflexiveDefaultModels260
import Yulang.GeneralReflexiveDefaultRun260
import Yulang.GeneralReflexiveDefaultRegression260
import Yulang.GeneralRebaseBodyActual260
import Yulang.GeneralRebaseRequestBodyKeys260
import Yulang.GeneralRebaseNamedRequest260
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseOutputKeys260.", "Yulang.GeneralRebaseOutputDecoder260.", "Yulang.GeneralOutputRebaseSource260.", "Yulang.GeneralOutputRebaseModels260.", "Yulang.GeneralOutputRebaseInstalled260.", "Yulang.GeneralOutputRebaseRun260.", "Yulang.GeneralOutputRebasePublic260.", "Yulang.GeneralRebaseOwnedOutputKeys260.", "Yulang.GeneralRebaseOutputFamily260.", "Yulang.GeneralRebaseOutputFamilyRun260.", "Yulang.GeneralOwnedOutputDecoder260.", "Yulang.GeneralOwnedOutputActual260.", "Yulang.GeneralDefaultRebaseBody260.", "Yulang.GeneralDefaultRebaseSource260.", "Yulang.GeneralDefaultRebaseModels260.", "Yulang.GeneralDefaultRebaseInstalled260.", "Yulang.GeneralDefaultRebaseRun260.", "Yulang.GeneralDefaultRebaseCompletion260.", "Yulang.GeneralDefaultRebasePublic260.", "Yulang.GeneralRebaseBodyDecoder260.", "Yulang.GeneralReflexiveDefaultSource260.", "Yulang.GeneralReflexiveDefaultModels260.", "Yulang.GeneralReflexiveDefaultRun260.", "Yulang.GeneralReflexiveDefaultRegression260.", "Yulang.GeneralRebaseBodyActual260.", "Yulang.GeneralRebaseRequestBodyKeys260.", "Yulang.GeneralRebaseNamedRequest260."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE260-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
