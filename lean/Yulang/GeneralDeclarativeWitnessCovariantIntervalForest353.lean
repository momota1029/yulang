import Yulang.GeneralDeclarativeWitnessCovariantInterval353
import Yulang.GeneralDeclarativeWitnessCovariantForest353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantIntervalForest353
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Valuation View HasView)
open GeneralDeclarativeWitnessCovariantInterval353 (Checked typed_interval exact_write_targets)
open GeneralDeclarativeWitnessCovariantForest353 (Environment Children ChildWire readChildren)
open GeneralDeclarativeWitnessCovariantSubtree353 (ordinarySource)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ classification classifications_exact classification_exact)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)

structure Wire where
  interval : GeneralDeclarativeWitnessCovariantInterval353.Wire
  rootOut : GeneralDeclarativeWitnessCompiler350.Wire
  children : List ChildWire

structure Accepted (p : Problem) (e : Environment p) (s : State) (w : Wire) (report : Report) where
  root : Checked p w.interval s w.rootOut
  ordinary : SourceBundle
  actual : compile (ordinarySource p) = some ordinary
  children : Children p e s 0 root.compiler.compiled.kids
  exact : agrees ⟨p.metadata.sourceInput,s,p.demand⟩
    (.selected root.facts.center.decl.id children.trees) report = true

def decode (p : Problem) (e : Environment p) (s : State) (w : Wire) (report : Report) :
    Option (Accepted p e s w report) := do
  let fixed ← GeneralDeclarativeWitnessCovariantInterval353.decode p w.interval s w.rootOut
  match chosen : compile (ordinarySource p) with
  | none => none
  | some childrenScope => do
    let forest ← readChildren p e s 0 fixed.compiler.compiled.kids w.children
    if checked : agrees ⟨p.metadata.sourceInput,s,p.demand⟩
        (.selected fixed.facts.center.decl.id forest.trees) report = true then
      pure ⟨fixed,childrenScope,chosen,forest,checked⟩
    else none

theorem semantic {p e s w report} (a : Accepted p e s w report) (m : Assignment) (v : Valuation)
    (fit : Models s m) (actual : ∀ row ∈ p.rows, HasView m v row) :
    (∃ lo center hi : View,
      v a.root.facts.arg.lower = some lo ∧ v a.root.facts.arg.center = some center ∧
      v a.root.facts.arg.upper = some hi ∧
      DeclaredSubtype (table w.interval.center.box) (View.head lo) (View.head center) ∧
      DeclaredSubtype (table w.interval.center.box) (View.head center) (View.head hi)) ∧
    (∀ span ∈ a.root.facts.ctx.spans,
      CommonNominalFullCarrier.Equivalent (m span.2.center).1
        (.union (m a.root.facts.center.anchor.first.valueName).1 (m a.root.facts.center.anchor.last.valueName).1)) ∧
    All₂ (Evidence (registry a.ordinary) (interpretation a.ordinary.snapshot) m)
      a.root.compiler.compiled.kids a.children.entries ∧
    report.result = .selected (.node a.root.facts.center.decl.id a.children.entries) ∧
    report.outputs = p.demand.outputs ∧
    w.rootOut.outputRows.map Equation.left = p.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ row ∈ w.rootOut.outputRows,Holds m row := by
  have prior := GeneralDeclarativeGrowth327.restrict
    ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp a.root.kept) m fit
  obtain ⟨l,c,h,ll,cc,hh,_,lh,rh⟩ := typed_interval a.root.facts m v prior actual
  have x := exact_report a.exact
  have eq : classification (.selected a.root.facts.center.decl.id a.children.trees) =
      .selected (.node a.root.facts.center.decl.id a.children.entries) :=
    (classification_exact ..).mpr (.selected ((classifications_exact ..).mp a.children.agree) (.selected rfl))
  exact ⟨⟨l,c,h,ll,cc,hh,lh,rh⟩,GeneralDeclarativeWitnessCovariantCompiler353.whole_in_each
    a.root.facts.center.anchor a.root.facts.center.names m prior,
    a.children.same_model a.actual m fit,x.2.1.trans eq,x.2.2,(exact_write_targets a.root m fit).2⟩

end Yulang.GeneralDeclarativeWitnessCovariantIntervalForest353
