import Yulang.GeneralDeclarativeWitnessMixedIsolation356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedReleaseMeaning356
open GeneralDeclarativeWitnessSpineNode355 (Node current_payload)
open GeneralDeclarativeWitnessCovariantOrigin353 (View Valuation Row HasView assigned)
open GeneralDeclarativeWitnessTypedJoint354 (shared author_rows)
open GeneralDeclarativeWitnessMixedSiblings356 (Child Sons Accepted MixedEvidence sound)
open GeneralDeclarativeWitnessMixedTyped356 (Typed exact_actual_center)
open GeneralDeclarativeWitnessMixedScope356 (ordinary_same_model)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary All₂)

def Crosses {s : State} {p : Node s} {e idx d plan w} (q : Typed p e idx d plan w)
    (m : Assignment) (v : Valuation) : Prop :=
  let reader := q.first.node.proof.compiled.readFrom.arg
  let association := q.first.issued.item
  q.first.node.origin.path = p.origin.path ++ [idx] ∧
  p.out.trace[plan.first.write]? = some (.typed association.typed.row) ∧
  p.address plan.first.write association.demand ∈ plan.first.authority.released ∧
  Supplies p.proof.compiled.readFrom.ctx.registry.roles p.proof.compiled.readFrom.ctx.decl
    association.demand.name (.explicit association.typed.authored) ∧
  reader.center = association.demand.target ∧
  ∃ x : View,
    v reader.center = some x ∧ x.tag = association.typed.tag ∧ x.box = association.typed.box ∧
    Common.Equivalent x.payload
      (.union (assigned m p.proof.compiled.readFrom.center.anchor.first.valueName).1
        (assigned m p.proof.compiled.readFrom.center.anchor.last.valueName).1)

theorem guaranteed_release {s : State} {p : Node s} {e idx d plan w} (q : Typed p e idx d plan w)
    (m : Assignment) (fit : Models s m) (v : Valuation) (all : ∀ row ∈ q.subtree.rows,HasView m v row) :
    Crosses q m v := by
  let it := q.first.issued.item
  have firstNode : q.first.node ∈ q.subtree.nodes := by cases q.subtree <;> exact List.mem_cons_self
  have in_ : it.typed.row ∈ q.first.node.input.rows := List.mem_append_right _ List.mem_cons_self
  obtain ⟨x,key,tag,box,whole⟩ := all it.typed.row (List.mem_flatMap.mpr ⟨_,firstNode,in_⟩)
  have center := exact_actual_center q.first
  have stored : it.typed.row.root = it.demand.target := rfl
  rw [stored,← center] at key
  have eq := current_payload q.first.issued m fit
  have joins := Common.equivalent_trans whole
    ⟨CommonNominalRegularErasure.subtype_monotone _ _ eq.1,CommonNominalRegularErasure.subtype_monotone _ _ eq.2⟩
  have ok := p.proof.compiled.readFrom.center.good
  have ids := (GeneralDeclarativeWitnessProblem349.splitAnd
    (GeneralDeclarativeWitnessProblem349.splitAnd ok).1).2
  have unique := (GeneralDeclarativeWitnessChecks349.identified ids).2.2.1
  exact ⟨q.first.path,q.first.issued.found,q.first.issued.grants,
    GeneralDeclarativeWitnessTypedOutput354.supplies it.typed unique,center,⟨x,key,tag,box,joins⟩⟩

def Branch {s : State} {p : Node s} {e idx d} (m : Assignment) (v : Valuation) : Child p e idx d → Prop
  | .typed q => Crosses q m v
  | .payload _q ex =>
    (∃ actual, d.arguments = [actual] ∧ actual.center = p.valueName ∧
      CommonNominalFullCarrier.Equivalent (m actual.center).1
        (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
          (m p.proof.compiled.readFrom.center.anchor.last.valueName).1)) ∧
    ex.actual.diagnostic.fixed.map GeneralDeclarativeWitnessForest350.Fixed.path =
      GeneralDeclarativeWitnessPathOrder352.preorder (p.origin.path ++ [idx]) ex.actual.diagnostic.tree

def group {s : State} {p : Node s} {e idx ds} (m : Assignment) (v : Valuation) : Sons p e idx ds → Prop
  | .nil => True
  | .cons one rest => Branch m v one ∧ group m v rest

theorem actual_branch_facts {s : State} {p : Node s} {e idx ds} (q : Sons p e idx ds)
    (m : Assignment) (fit : Models s m) (v : Valuation) (all : ∀ row ∈ q.rows,HasView m v row) :
    group m v q := by
  induction q with
  | nil => trivial
  | cons one more ih =>
    refine ⟨?_,ih (fun row h => all row (List.mem_append_right _ h))⟩
    have prev : ∀ row ∈ one.rows,HasView m v row := fun row h => all row (List.mem_append_left _ h)
    cases one with
    | typed x => exact guaranteed_release x m fit v prev
    | payload read result => exact ⟨GeneralDeclarativeWitnessPayloadRoute356.ordinary_payload_law read m fit,result.paths⟩

theorem same_models_separate_receipts {s : State} {p : Node s} {e out} (a : Accepted p e out)
    (m : Assignment) (fit : Models s m) :
    ∃ v,
      GeneralDeclarativeWitnessTypedEvidence355.Local m v p ∧
      All₂ (MixedEvidence p m v) p.proof.compiled.children a.children.dictionaries ∧
      group m v a.children := by
  let v := shared p.input (p.input.rows ++ a.children.rows) m
  have h : ∀ row ∈ p.input.rows ++ a.children.rows,HasView m v row := author_rows a.compatible m
  have root := GeneralDeclarativeWitnessNominalSpine355.node_is_sound p m fit v
    (fun r used => h r (List.mem_append_left _ used))
  have next : ∀ row ∈ a.children.rows,HasView m v row := fun row seen => h row (List.mem_append_right _ seen)
  exact ⟨v,GeneralDeclarativeWitnessTypedEvidence355.all_input_binders_in_same_model p m fit v root,
    a.children.same_model m fit v next,actual_branch_facts a.children m fit v next⟩

end Yulang.GeneralDeclarativeWitnessMixedReleaseMeaning356
