import Yulang.GeneralDeclarativeWitnessRecursiveTree356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecursiveSound356
open GeneralDeclarativeWitnessRecursiveMixed356 (Tree Branches)
open GeneralDeclarativeWitnessRecursiveTree356 (rows otherRows dictionary dictionaries view exact_tree)
open GeneralDeclarativeWitnessMixedTyped356 (At exact_actual_center)
open GeneralDeclarativeWitnessMixedScope356 (Ordinary ordinary_same_model)
open GeneralDeclarativeWitnessPayloadRoute356 (Route ordinary_payload_law)
open GeneralDeclarativeWitnessSpineNode355 (Node current_payload)
open GeneralDeclarativeWitnessCovariantOrigin353 (HasView Valuation View assigned)
open GeneralDeclarativeWitnessTypedJoint354 (shared author_rows compatible)
open GeneralDeclarativeWitnessTypedEvidence355 (Local all_input_binders_in_same_model)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)

def LocalPayload {s : State} {p : Node s} {e i d r} (_read : Route p i d)
    (a : Ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [i]) d r) (m : Assignment) : Prop :=
  GeneralDeclarativeExactDictionary337.Evidence (registry a.actual.global.table)
    (interpretation a.actual.global.table.snapshot) m d a.dictionary ∧
  (∃ cap, d.arguments = [cap] ∧ cap.center = p.valueName ∧
    CommonNominalFullCarrier.Equivalent (m cap.center).1
      (.union (m p.proof.compiled.readFrom.center.anchor.first.valueName).1
        (m p.proof.compiled.readFrom.center.anchor.last.valueName).1)) ∧
  (∀ f ∈ a.actual.diagnostic.fixed,f.equations.map Equation.left =
    f.demand.outputs.map GeneralSourceState.Output.target ∧ ∀ q ∈ f.equations,Holds m q) ∧
  a.actual.diagnostic.fixed.map Fixed.path =
    GeneralDeclarativeWitnessPathOrder352.preorder (p.origin.path ++ [i]) r.tree

def NominalUse {s : State} {p : Node s} {e i d a w} (edge : At p e i d a w) (m : Assignment) (v : Valuation) : Prop :=
  let item := edge.issued.item
  let center := edge.node.proof.compiled.readFrom.arg.center
  center = item.demand.target ∧ edge.node.origin.path = p.origin.path ++ [i] ∧
  p.out.trace[a.write]? = some (.typed item.typed.row) ∧
  p.address a.write item.demand ∈ a.authority.released ∧
  ∃ atCenter : View, v center = some atCenter ∧ atCenter.tag = item.typed.tag ∧ atCenter.box = item.typed.box ∧
    Common.Equivalent atCenter.payload
      (.union (assigned m p.proof.compiled.readFrom.center.anchor.first.valueName).1
        (assigned m p.proof.compiled.readFrom.center.anchor.last.valueName).1)

theorem nominal_read {s : State} {p : Node s} {e i d a w} (edge : At p e i d a w) (m : Assignment)
    (fit : Models s m) (v : Valuation) (actual : ∀ r ∈ edge.node.input.rows,HasView m v r) :
    NominalUse edge m v := by
  let it := edge.issued.item
  obtain ⟨seen,at_,tag,box,payload⟩ := actual it.typed.row (List.mem_append_right _ List.mem_cons_self)
  have mapped := exact_actual_center edge
  have fixed : it.typed.row.root = it.demand.target := rfl
  rw [fixed,← mapped] at at_
  have eq := current_payload edge.issued m fit
  exact ⟨mapped,edge.path,edge.issued.found,edge.issued.grants,⟨seen,at_,tag,box,
    Common.equivalent_trans payload
    ⟨CommonNominalRegularErasure.subtype_monotone _ _ eq.1,CommonNominalRegularErasure.subtype_monotone _ _ eq.2⟩⟩⟩

mutual
inductive Evident (s : State) (m : Assignment) (v : Valuation) :
    Demand → Dictionary → Prop where
  | node (p : Node s) (localFacts : Local m v p)
    (children : Lists s m v p p.proof.compiled.children ds) :
      Evident s m v p.input.demand (.node p.name ds)
inductive BranchEvidence (s : State) (m : Assignment) (v : Valuation) :
    Node s → Demand → Dictionary → Prop where
  | typed {p : Node s} (route : At p e i d a w) : NominalUse route m v →
      Evident s m v d dict → BranchEvidence s m v p d dict
  | payload {p : Node s} {e i d out} (route : Route p i d)
    (a : Ordinary e p.input.metadata.sourceInput s (p.origin.path ++ [i]) d out) :
      LocalPayload route a m → BranchEvidence s m v p d a.dictionary
inductive Lists (s : State) (m : Assignment) (v : Valuation) :
    Node s → List Demand → List Dictionary → Prop where
  | nil : Lists s m v p [] []
  | cons : BranchEvidence s m v p d k → Lists s m v p ds ks → Lists s m v p (d::ds) (k::ks)
end

theorem meaning {s : State} {e p} (t : @Tree s e p) (m : Assignment) (fit : Models s m) (v : Valuation)
    (support : ∀ r ∈ rows t,HasView m v r) : Evident s m v p.input.demand (dictionary t) := by
  refine @Tree.rec s e
    (fun p t => (∀ row ∈ rows t,HasView m v row) → Evident s m v p.input.demand (dictionary t))
    (fun p _ ds xs => (∀ row ∈ otherRows xs,HasView m v row) →
      Lists s m v p ds (dictionaries xs))
    ?_ ?_ ?_ ?_ p t support
  · intro p role xs ih support
    rw [dictionary.eq_def]
    have columns : ∀ r ∈ p.input.rows ++ otherRows xs,HasView m v r := by simpa only [rows.eq_def] using support
    have specific := GeneralDeclarativeWitnessNominalSpine355.node_is_sound p m fit v
      (fun r selected => columns r (List.mem_append_left _ selected))
    exact .node p (all_input_binders_in_same_model p m fit v specific)
      (ih (fun r selected => columns r (List.mem_append_right _ selected)))
  · intro i p _
    rw [dictionaries.eq_def]
    exact .nil
  · intro i d ds p a w route child rest mine remaining support
    rw [dictionaries.eq_def]
    have opts : ∀ r ∈ rows child ++ otherRows rest,HasView m v r := by
      rw [otherRows.eq_def] at support
      exact support
    have first : ∀ r ∈ rows child,HasView m v r := fun r found => opts r (List.mem_append_left _ found)
    have rootRows : ∀ r ∈ route.node.input.rows,HasView m v r := by
      cases child with
      | typed _ ys =>
        intro row found
        apply first
        rw [rows.eq_def]
        exact List.mem_append_left _ found
    exact .cons (.typed route (nominal_read route m fit v rootRows) (mine first))
      (remaining (fun r seen => opts r (List.mem_append_right _ seen)))
  · intro i d ds p report route observed rest next support
    rw [dictionaries.eq_def]
    have got := ordinary_same_model observed m fit
    have all : LocalPayload route observed m := ⟨got.1,ordinary_payload_law route m fit,got.2.1,got.2.2.2⟩
    exact .cons (.payload route observed all)
      (next (by rw [otherRows.eq_def] at support; exact support))

theorem one_model_for_whole_tree {s : State} {e p} (t : @Tree s e p)
    (joint : compatible (rows t) = true) (m : Assignment) (fit : Models s m) :
    ∃ v : Valuation, Evident s m v p.input.demand (dictionary t) :=
  ⟨shared p.input (rows t) m,meaning t m fit _ (author_rows joint m)⟩

end Yulang.GeneralDeclarativeWitnessRecursiveSound356
