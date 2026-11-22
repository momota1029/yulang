import Yulang.GeneralDeclarativeWitnessCovariantIntervalForest353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantCanonical353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row View HasView Valuation assigned)
open GeneralDeclarativeWitnessCovariantForest353 (Environment)
open GeneralDeclarativeWitnessCovariantIntervalForest353 (Wire Accepted decode semantic)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessTree349 (Report)
open CommonRoleOutermostResolver (All₂)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open GeneralSourceMetadataExprDomain291 (bind_success)

theorem find_root {rs : List Row} (uniq : (rs.map Row.root).Nodup) {r : Row} (used : r ∈ rs) :
    rs.find? (fun x => x.root == r.root) = some r := by
  induction rs with
  | nil => cases used
  | cons h tail ih =>
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp uniq
    rcases List.mem_cons.mp used with rfl|rest
    · simp
    · have miss : h.root ≠ r.root := by
        intro same
        apply fresh
        rw [same]
        exact List.mem_map_of_mem rest
      simpa [List.find?_cons,miss] using ih nodup rest

def valuation (p : Problem) (m : Assignment) : Valuation := fun n =>
  (p.rows.find? (fun x => x.root == n)).map fun r => ⟨r.tag,r.box,(assigned m r.valueName).1⟩

theorem view_for_every_model (p : Problem) (m : Assignment) (uniq : (p.rows.map Row.root).Nodup) :
    ∀ r ∈ p.rows, HasView m (valuation p m) r := by
  intro r used
  exact ⟨⟨r.tag,r.box,(assigned m r.valueName).1⟩,by simp [valuation,find_root uniq used],rfl,rfl,Common.equivalent_refl _⟩

theorem rows_at_read {p : Problem} {w : GeneralDeclarativeWitnessCovariantOrigin353.Wire} {a}
    (found : GeneralDeclarativeWitnessCovariantOrigin353.read p w = some a) :
    (p.rows.map Row.root).Nodup := by
  unfold GeneralDeclarativeWitnessCovariantOrigin353.read at found
  obtain ⟨metadata,_,next⟩ := bind_success found
  obtain ⟨head,_,checked⟩ := bind_success next
  split at checked
  · split at checked
    · rename_i yes
      exact of_decide_eq_true (splitAnd yes).1
    · cases checked
  · cases checked

theorem rows_at_prepare {p : Problem} {w : GeneralDeclarativeWitnessCovariantOrigin353.Wire} {a}
    (found : GeneralDeclarativeWitnessCovariantCompiler353.prepare p w = some a) :
    (p.rows.map Row.root).Nodup := by
  unfold GeneralDeclarativeWitnessCovariantCompiler353.prepare at found
  obtain ⟨_,r,_⟩ := bind_success found
  exact rows_at_read r

theorem rows_at_interval {p : Problem} {w : GeneralDeclarativeWitnessCovariantInterval353.Wire} {a}
    (found : GeneralDeclarativeWitnessCovariantInterval353.read p w = some a) :
    (p.rows.map Row.root).Nodup := by
  unfold GeneralDeclarativeWitnessCovariantInterval353.read at found
  split at found
  · obtain ⟨_,b,_⟩ := bind_success found
    have uniq := rows_at_prepare b
    exact uniq
  · cases found

theorem rows_at_forest {p : Problem} {e : Environment p} {s : State} {w : Wire} {report : Report} {a}
    (found : decode p e s w report = some a) :
    (p.rows.map Row.root).Nodup := by
  unfold decode at found
  obtain ⟨_,atRoot,_⟩ := bind_success found
  unfold GeneralDeclarativeWitnessCovariantInterval353.decode at atRoot
  obtain ⟨_,verified,_⟩ := bind_success atRoot
  exact rows_at_interval verified

/-- No model-assignment field is supplied by the checker wire. For
each model of the exact ordinary current state there is a canonical
typed view computed from the independent source rows, and the actual
interval, children, and writes are sound simultaneously. -/
theorem all_models {p : Problem} {e : Environment p} {s : State} {w : Wire} {report : Report}
    {a : Accepted p e s w report} (certificate : decode p e s w report = some a)
    (m : Assignment) (fit : Models s m) :
    (∃ low current high : View,
      valuation p m a.root.facts.arg.lower = some low ∧
      valuation p m a.root.facts.arg.center = some current ∧
      valuation p m a.root.facts.arg.upper = some high ∧
      DeclaredSubtype (table w.interval.center.box) (View.head low) (View.head current) ∧
      DeclaredSubtype (table w.interval.center.box) (View.head current) (View.head high)) ∧
    (∀ span ∈ a.root.facts.ctx.spans,
      CommonNominalFullCarrier.Equivalent (m span.2.center).1
        (.union (m a.root.facts.center.anchor.first.valueName).1 (m a.root.facts.center.anchor.last.valueName).1)) ∧
    All₂ (Evidence (registry a.ordinary) (interpretation a.ordinary.snapshot) m)
      a.root.compiler.compiled.kids a.children.entries ∧
    report.result = .selected (.node a.root.facts.center.decl.id a.children.entries) ∧
    report.outputs = p.demand.outputs ∧
    w.rootOut.outputRows.map Equation.left = p.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ row ∈ w.rootOut.outputRows,Holds m row :=
  semantic a m (valuation p m) fit (view_for_every_model p m (rows_at_forest certificate))

end Yulang.GeneralDeclarativeWitnessCovariantCanonical353
