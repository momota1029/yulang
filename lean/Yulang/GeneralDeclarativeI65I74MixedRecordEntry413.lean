import Yulang.GeneralDeclarativeI65I74MixedRecordScan413
import Yulang.GeneralDeclarativeI65I74MixedRecordReport413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open Checker408 (Problem Result)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

structure MixedWire where
  root : RootWire
  path : FieldCycleWire

structure MixedVerified (p : Problem) where
  rejection : MixedRecordRejection p.state p.root
  rootSafe : ¬RootCycle p.state p.root

/-- Only raw path/row locators are supplied by the witness. Checked
candidates and the deep-candidate ordinal come from the whole list. -/
def replayMixed413 (p : Problem) (w : MixedWire) : Option (MixedVerified p) := do
  let view ← rootRead413 p w.root
  let rows := visible p.state.core p.root
  if count : 2 ≤ rows.length then
    if distinct : (rows.map Declaration.id).Nodup then
      let shape ← scanAll413 view.actual rows
      match shape with
      | .plain _ => none
      | .mixed tape =>
        if cycle : checkCycleAt412 p.state.core.current.ordinary view.actual.site w.path = true then
          some ⟨⟨view.actual,tape,count,distinct,cycle_at_sound412 cycle⟩,view.safe⟩
        else none
    else none
  else none

theorem mixed_scope_rejects_before_election413 (p : Problem) (proof : MixedVerified p) :
    ClassifiedAs p.state p.root Check408.rawReport := by
  let exactTrace : SourceTrace R5 p.state p.root .rejected none :=
    .other .rejected proof.rootSafe (.inr ⟨rfl,rfl,⟨proof.rejection⟩⟩) .nil
  exact ⟨none,exactTrace,.rejected,rfl⟩

inductive Witness where
  | previous (old : RecordK2412.Witness)
  | mixedHead (w : MixedWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => RecordK2412.check p r w
  | .mixedHead w => (replayMixed413 p w).isSome && Check408.matchesNoWrites r .rejected .rejected
  | .unsupported => false

theorem previous_entry_unchanged413 (p : Problem) (r : Result) (old : RecordK2412.Witness) :
    check p r (.previous old) = RecordK2412.check p r old := rfl

theorem checked_mixed_head_reflects_original413 (p : Problem) (r : Result) (w : MixedWire)
    (success : check p r (.mixedHead w) = true) :
    ∃ v : MixedVerified p, replayMixed413 p w = some v ∧ r = Check408.rawReport := by
  obtain ⟨source,report⟩ := splitAnd success
  cases captured : replayMixed413 p w with
  | none => simp [captured] at source
  | some v =>
    obtain ⟨tree,verdict,output⟩ := Check408.matchesNoWrites_exact408.mp report
    refine ⟨v,rfl,?_⟩
    cases r
    simp only at tree verdict output
    subst_vars
    rfl

theorem checked_entry_has_exact_original_report413 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts413 (RecordK2412.check_sound p r old yes).1
  | mixedHead fresh =>
    obtain ⟨v,_,same⟩ := checked_mixed_head_reflects_original413 p r fresh yes
    exact same ▸ mixed_scope_rejects_before_election413 p v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have exact := checked_entry_has_exact_original_report413 p r w yes
  refine ⟨exact,?_⟩
  obtain ⟨e,t,sums,out⟩ := exact
  exact fun m fit => ⟨e,t,sums,out,mixed_R5_trace_model_meaning413 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
