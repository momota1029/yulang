import Yulang.GeneralDeclarativeWitnessSpineNode355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalSpine355
open GeneralDeclarativeWitnessSpineNode355 (Node Step Author Send next)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation HasView Row)
open GeneralDeclarativeWitnessGrandchildContinuity355 (realInterval)
open GeneralDeclarativeWitnessTypedJoint354 (compatible shared author_rows)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Dictionary Result classification classification_exact classifications_exact All₂)

inductive Code where
  | leaf
  | send (here : Send) (rest : Code)

inductive Checked {s : State} : Node s → Type where
  | leaf {p : Node s} (empty : p.proof.compiled.children = []) : Checked p
  | send {p : Node s} (a : Author) (wire : Send) (edge : Step p a wire) :
      Checked edge.node → Checked p

/-- Recursion on finite supplied evidence, never on solver evaluation. -/
def read {s : State} (p : Node s) (authored : List Author) (code : Code) : Option (Checked p) :=
  match code,authored with
  | .leaf,[] =>
    if noChildren : p.proof.compiled.children.isEmpty = true then
      some (.leaf (List.isEmpty_iff.mp noChildren))
    else none
  | .send here rest,a::more => do
    let edge ← next p a here
    let proof ← read edge.node more rest
    pure (.send a here edge proof)
  | _,_ => none
termination_by sizeOf code

def Checked.nodes {s : State} {p : Node s} : Checked p → List (Node s)
  | .leaf _ => [p]
  | .send _ _ _ tail => p :: tail.nodes

def Checked.tree {s : State} {p : Node s} : Checked p → Tree
  | .leaf _ => .selected p.name []
  | .send _ _ _ tail => .selected p.name [tail.tree]

def Checked.dictionary {s : State} {p : Node s} : Checked p → Dictionary
  | .leaf _ => .node p.name []
  | .send _ _ _ tail => .node p.name [tail.dictionary]

theorem classified {s : State} {p : Node s} (ok : Checked p) :
    classification ok.tree = .selected ok.dictionary := by
  induction ok with
  | leaf empty => rfl
  | @send middle a wire edge tail ih =>
    exact (classification_exact ..).mpr (.selected
      (.cons ((classification_exact ..).mp ih) .nil) (.selected rfl))

def Checked.rows {s : State} {p : Node s} (ok : Checked p) : List Row :=
  ok.nodes.flatMap (fun v => v.input.rows)

def NodeMeaning {s : State} (m : Assignment) (v : Valuation) (p : Node s) : Prop :=
  realInterval v p.proof.compiled.readFrom.arg p.head.center.box ∧
  p.out.kids = p.proof.compiled.children.map GeneralDeclarativeWitnessCompiler350.printDemand ∧
  p.out.trace.map Write.target = p.input.demand.outputs.map GeneralSourceState.Output.target ∧
  (∀ e ∈ p.proof.compiled.whereRows,Holds m e) ∧
  (∀ e ∈ ordinary p.out.trace,Holds m e)

theorem node_is_sound {s : State} (p : Node s) (m : Assignment) (fit : Models s m)
    (v : Valuation) (author : ∀ row ∈ p.input.rows,HasView m v row) :
    NodeMeaning m v p := by
  have writes := GeneralDeclarativeWitnessTypedRangeWriter354.writes_and_children p.proof m fit
  obtain ⟨l,c,h,ll,cc,hh,_,lh,rh⟩ :=
    GeneralDeclarativeWitnessTypedRangeWriter354.range_in_same_model p.proof m fit v author
  exact ⟨⟨l,c,h,ll,cc,hh,lh,rh⟩,writes.2.1,writes.1,writes.2.2⟩

theorem all_same_model {s : State} {p : Node s} (ok : Checked p)
    (joint : compatible ok.rows = true) (m : Assignment) (fit : Models s m) :
    ∃ v : Valuation, ∀ n ∈ ok.nodes,NodeMeaning m v n := by
  let v := shared p.input ok.rows m
  refine ⟨v,fun n used => node_is_sound n m fit v ?_⟩
  intro row visible
  exact author_rows joint m row (List.mem_flatMap.mpr ⟨n,used,visible⟩)

theorem actual_payload_names_are_unchanged {s : State} {p : Node s} (ok : Checked p) :
    ∀ n ∈ ok.nodes,n.valueName = p.valueName := by
  induction ok with
  | leaf empty =>
    intro n h
    cases List.mem_singleton.mp h
    rfl
  | send a route here tail ih =>
    intro n h
    change n ∈ _ :: tail.nodes at h
    rcases List.mem_cons.mp h with same|later
    · rw [same]
    · exact (ih n later).trans (GeneralDeclarativeWitnessSpineNode355.no_payload_name_renaming here)

def Checked.hops {s : State} {p : Node s} : Checked p → List (Nat × Nat × List Nat)
  | .leaf _ => []
  | .send _ code edge tail =>
    (edge.accepted.item.demand.target,edge.node.proof.compiled.readFrom.arg.center,code.path) :: tail.hops

theorem real_center_along_retained_joined_spine {s : State} {p : Node s} (ok : Checked p)
    (joined : ∀ n ∈ ok.nodes,
      n.proof.compiled.readFrom.center.decl.head = [GeneralDeclarativeWitnessCovariantHead352.rawPattern]) :
    ∀ edge ∈ ok.hops,edge.1 = p.valueName ∧ edge.2.1 = p.valueName := by
  induction ok with
  | leaf empty => intro edge missing; cases missing
  | @send middle a code edge tail ih =>
    have branch := joined middle List.mem_cons_self
    have same := GeneralDeclarativeWitnessSpineNode355.joined_edge_same_literal edge branch
    have checked := GeneralDeclarativeWitnessSpineNode355.exact_physical_center edge
    have rest := ih (fun n used => joined n (List.mem_cons_of_mem _ used))
    intro triple more
    rcases List.mem_cons.mp more with first|later
    · cases first
      exact ⟨same,checked.trans same⟩
    · have kept := GeneralDeclarativeWitnessSpineNode355.no_payload_name_renaming edge
      exact ⟨(rest _ later).1.trans kept,(rest _ later).2.trans kept⟩

end Yulang.GeneralDeclarativeWitnessNominalSpine355
