import Yulang.GeneralDeclarativeWitnessSpineFrontLedger355
import Yulang.GeneralDeclarativeWitnessOldPremises355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSpineEdgeMeaning355
open GeneralDeclarativeWitnessSpineNode355 (Node Step Author Send current_payload)
open GeneralDeclarativeWitnessNominalSpine355 (Checked)
open GeneralDeclarativeWitnessSpineFront355 (Found)
open GeneralDeclarativeWitnessTypedJoint354 (compatible shared author_rows)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row View HasView Valuation assigned)
open GeneralDeclarativeWitnessTypedEvidence355 (Evidence compose)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeHead320 (State Models)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralNominalCommonBridge (Assignment)

structure Emission (s : State) where
  parent : Node s
  author : Author
  wire : Send
  exact : Step parent author wire

def Checked.emissions {s : State} {p : Node s} : Checked p → List (Emission s)
  | .leaf _ => []
  | .send a w first rest => ⟨p,a,w,first⟩ :: emissions rest

theorem to_child_node {s : State} {p : Node s} (ok : Checked p) :
    ∀ edge ∈ Checked.emissions ok, edge.exact.node ∈ ok.nodes := by
  induction ok with
  | leaf empty => intro good no; cases no
  | @send p a w q rest ih =>
    intro edge there
    rcases List.mem_cons.mp there with rfl|later
    · apply List.mem_cons_of_mem
      cases rest <;> exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih edge later)

def Meaning {s : State} (m : Assignment) (v : Valuation) (e : Emission s) : Prop :=
  let item := e.exact.accepted.item
  let fact := item.typed
  let q := e.parent.proof.compiled.readFrom
  let name := e.exact.node.proof.compiled.readFrom.arg.center
  e.parent.out.trace[e.author.write]? = some (.typed fact.row) ∧
  (e.parent.address e.author.write item.demand) ∈ e.author.authority.released ∧
  Supplies q.ctx.registry.roles q.ctx.decl item.demand.name (.explicit fact.authored) ∧
  name = item.demand.target ∧
  ∃ atName : View,
    v name = some atName ∧ atName.tag = fact.tag ∧ atName.box = fact.box ∧
    Common.Equivalent atName.payload
      (.union (assigned m q.center.anchor.first.valueName).1 (assigned m q.center.anchor.last.valueName).1)

theorem one_edge {s : State} (e : Emission s) (m : Assignment) (fit : Models s m) (v : Valuation)
    (seen : ∀ row ∈ e.exact.node.input.rows,HasView m v row) : Meaning m v e := by
  let item := e.exact.accepted.item
  have has : item.typed.row ∈ e.exact.node.input.rows := List.mem_append_right _ List.mem_cons_self
  obtain ⟨atName,at_,tag,box,payload⟩ := seen _ has
  have literal := GeneralDeclarativeWitnessSpineNode355.exact_physical_center e.exact
  have rowAt : item.typed.row.root = item.demand.target := rfl
  rw [rowAt,← literal] at at_
  have current := current_payload e.exact.accepted m fit
  have joins := Common.equivalent_trans payload
    ⟨CommonNominalRegularErasure.subtype_monotone _ _ current.1,
     CommonNominalRegularErasure.subtype_monotone _ _ current.2⟩
  have checked := e.parent.proof.compiled.readFrom.center.good
  have ids := (GeneralDeclarativeWitnessProblem349.splitAnd
    (GeneralDeclarativeWitnessProblem349.splitAnd checked).1).2
  have unique := (GeneralDeclarativeWitnessChecks349.identified ids).2.2.1
  exact ⟨e.exact.accepted.found,e.exact.accepted.grants,
    GeneralDeclarativeWitnessTypedOutput354.supplies item.typed unique,literal,
    ⟨atName,at_,tag,box,joins⟩⟩

theorem same_view_for_authorized_tree {p s w} (a : Found p s w) (m : Assignment) (fit : Models s m) :
    ∃ v : Valuation,
      Evidence s m v p.problem.demand a.checked.dictionary ∧
      ∀ edge ∈ Checked.emissions a.checked,Meaning m v edge := by
  let v := shared a.root.input a.checked.rows m
  have known : ∀ n ∈ a.checked.nodes, ∀ row ∈ n.input.rows,HasView m v row := by
    intro node place row seen
    exact author_rows a.mentions m row (List.mem_flatMap.mpr ⟨node,place,seen⟩)
  have full := compose a.checked m fit v (fun n place =>
    GeneralDeclarativeWitnessNominalSpine355.node_is_sound n m fit v (known n place))
  have changed := congrArg GeneralDeclarativeWitnessCovariantOrigin353.Problem.demand a.sameProblem
  have same : a.root.input.demand = p.problem.demand := changed
  exact ⟨v,same ▸ full,fun edge place => one_edge edge m fit v
    (known _ (to_child_node a.checked edge place))⟩

end Yulang.GeneralDeclarativeWitnessSpineEdgeMeaning355
