import Yulang.GeneralDeclarativeWitnessNominalSpine355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalSpineWhole355
open GeneralDeclarativeWitnessSpineNode355 (Node Author)
open GeneralDeclarativeWitnessNominalSpine355 (Code Checked NodeMeaning classified all_same_model)
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeWitnessTypedJoint354 (compatible)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary classification classification_exact)

structure Seed where
  startVersion : Nat
  authors : List Author

def selectedTree {i s w} (a : Linked i s w) {version : Nat} (q : Checked (Node.ofFirst a version)) : Tree :=
  .selected a.writer.output.source.decl.id [q.tree]

def selectedDictionary {i s w} (a : Linked i s w) {version : Nat}
    (q : Checked (Node.ofFirst a version)) : Dictionary :=
  .node a.writer.output.source.decl.id [q.dictionary]

structure Found {i s w} (a : Linked i s w) (seed : Seed) (report : Report) where
  node : Checked (Node.ofFirst a seed.startVersion)
  single : a.writer.output.children = [a.child]
  compatible : compatible node.rows = true
  exact : agrees ⟨i.producer.metadata.sourceInput,s,i.producer.demand⟩ (selectedTree a node) report = true

def run {i s w} (a : Linked i s w) (seed : Seed) (code : Code) (report : Report) :
    Option (Found a seed report) := do
  let proof ← GeneralDeclarativeWitnessNominalSpine355.read (Node.ofFirst a seed.startVersion) seed.authors code
  if ord : a.writer.output.children.map GeneralDeclarativeWitnessCompiler350.printDemand =
       [GeneralDeclarativeWitnessCompiler350.printDemand a.child] then
    if shared : compatible proof.rows = true then
      if reportOK : agrees ⟨i.producer.metadata.sourceInput,s,i.producer.demand⟩ (selectedTree a proof) report =
          true then
        pure ⟨proof,GeneralDeclarativeWitnessCompiler350.map_injective
          GeneralDeclarativeWitnessCompiler350.print_injective ord,shared,reportOK⟩
      else none
    else none
  else none

theorem sound {i s w} {a : Linked i s w} {seed : Seed} {report : Report} (q : Found a seed report)
    (m : Assignment) (fit : Models s m) :
    report.tree = selectedTree a q.node ∧ report.result = .selected (selectedDictionary a q.node) ∧
    report.outputs = i.producer.demand.outputs ∧
    w.writer.trace.map Write.target = i.producer.demand.outputs.map GeneralSourceState.Output.target ∧
    (∀ eq ∈ ordinary w.writer.trace,Holds m eq) ∧
    ∃ v, ∀ n ∈ q.node.nodes,NodeMeaning m v n := by
  have reportOK := exact_report q.exact
  have checked := GeneralDeclarativeWitnessTypedPacket354.exact a.writer m fit
  have joined : classification (selectedTree a q.node) = .selected (selectedDictionary a q.node) :=
    (classification_exact ..).mpr (.selected
      (.cons ((classification_exact ..).mp (classified q.node)) .nil) (.selected rfl))
  exact ⟨reportOK.1,reportOK.2.1.trans joined,reportOK.2.2,checked.1,checked.2,
    all_same_model q.node q.compatible m fit⟩

end Yulang.GeneralDeclarativeWitnessNominalSpineWhole355
