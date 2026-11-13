import Yulang.GeneralDictionaryOrdinary168Relocation
import Yulang.GeneralDictionaryMixed168Tree
import Yulang.GeneralDictionaryMixed168Display
import Lean

/-! Read-only dependency/type audit for mixed structural certificates. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryOrdinary168Relocation, `Yulang.GeneralDictionaryMixed168Tree, `Yulang.GeneralDictionaryMixed168Display]
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

#check @Yulang.GeneralDictionaryOrdinary168Relocation.report_is_move
#check @Yulang.GeneralDictionaryOrdinary168Relocation.extension_at
#check @Yulang.GeneralDictionaryOrdinary168Relocation.packet_relocates
#check @Yulang.GeneralDictionaryMixed168Tree.current_evidence
#check @Yulang.GeneralDictionaryMixed168Tree.of_relocated_tree
#check @Yulang.GeneralDictionaryMixed168Display.parent_relocates
#check @Yulang.GeneralDictionaryMixed168Display.structural_tree
#check @Yulang.GeneralDictionaryMixed168Display.interpreted_dictionary
#check @Yulang.GeneralDictionaryMixed168Display.mixed_not_recorded
#check @Yulang.GeneralDictionaryMixed168Display.nonvacuous_interpretation
