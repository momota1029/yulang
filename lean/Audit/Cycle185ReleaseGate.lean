import Yulang.GeneralNominalHeadSemanticTransport185
import Yulang.GeneralNominalHeadBinderIdentity185
import Yulang.GeneralNominalHeadCandidateReadback185
import Yulang.GeneralNominalHeadCoreCoverage185
import Yulang.GeneralNominalHeadCoreOverlap185
import Yulang.GeneralNominalHeadEffectCore185
import Yulang.GeneralNominalHeadEffectReadback185
import Yulang.GeneralNominalHeadEffectsOrigin185
import Yulang.GeneralNominalHeadFullOverlap185
import Yulang.GeneralNominalHeadFullProducer185
import Yulang.GeneralNominalHeadHistoricalExtension185
import Yulang.GeneralNominalHeadOutputSupport185
import Yulang.GeneralNominalHeadPacketSupport185
import Yulang.GeneralNominalHeadRawSeparation185
import Yulang.GeneralNominalHeadReadback185
import Yulang.GeneralNominalHeadRootExtension185
import Yulang.GeneralNominalHeadRootOverlap185
import Yulang.GeneralNominalHeadSiteCoherence185
import Yulang.GeneralNominalHeadSiteOrigin185
import Yulang.GeneralNominalHeadSiteSupport185
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "185" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
