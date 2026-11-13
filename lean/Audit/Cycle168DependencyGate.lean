import Yulang.GeneralDictionarySource168Transport
import Yulang.GeneralDictionaryActual168Transport
import Yulang.GeneralDictionary168SourceGuard
import Lean

/-! Read-only dependency/type audit; no production declarations are introduced. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionarySource168Transport, `Yulang.GeneralDictionaryActual168Transport, `Yulang.GeneralDictionary168SourceGuard]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"

#check @Yulang.GeneralDictionarySource168Transport.capture_seed
#check @Yulang.GeneralDictionarySource168Transport.branch_relocated
#check @Yulang.GeneralDictionarySource168Transport.node_relocated
#check @Yulang.GeneralDictionarySource168Transport.actual_schemas
#check @Yulang.GeneralDictionarySource168Transport.actual_producer_branch
#check @Yulang.GeneralDictionary168SourceGuard.head_extension
#check @Yulang.GeneralDictionary168SourceGuard.ready_steps
#check @Yulang.GeneralDictionary168SourceGuard.reads_extended
#check @Yulang.GeneralDictionary168SourceGuard.readsMany_extended
#check @Yulang.GeneralDictionary168SourceGuard.decision_steps
#check @Yulang.GeneralDictionary168SourceGuard.evidence_and_guard_steps
#check @Yulang.GeneralDictionary168SourceGuard.container_install_ordinary
#check @Yulang.GeneralDictionary168SourceGuard.source_consumer_guard
#check @Yulang.GeneralDictionary168SourceGuard.source_consumer_continuation
#check @Yulang.GeneralDictionary168SourceGuard.source_consumer_nonvacuous
#check @Yulang.GeneralDictionarySource168Transport.actual_sources
#check @Yulang.GeneralDictionarySource168Transport.actual_seed
#check @Yulang.GeneralDictionarySource168Transport.actual_current_evidence
