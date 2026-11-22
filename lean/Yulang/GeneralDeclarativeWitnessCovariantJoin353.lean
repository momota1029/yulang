import Yulang.GeneralDeclarativeWitnessCovariantForest353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantJoin353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Anchored View Valuation HasView ModelsAt)
open GeneralDeclarativeWitnessCovariantMetadata353 (table table_key)
open GeneralDeclarativeWitnessCovariantViews353 (views actual_box_order)
open CommonDeclaredNominalInspection (DeclaredSubtype declared_subtype_exact)
open CommonNominalHeads (Head)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWitnessCovariantForest353 (Environment Accepted well_formed)
open GeneralDeclarativeWitnessCovariantCompiler353 (confirmed retained)
open GeneralDeclarativeWitnessCovariantSubtree353 (ordinarySource)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open CommonRoleOutermostResolver (All₂ Dictionary)

theorem ordinary_scope_exact (p : Problem) {parent : SourceBundle}
    (built : compile p.metadata.sourceInput = some parent) :
    compile (ordinarySource p) =
      some {parent with declarations := parent.declarations.filter (fun d => d.role != p.demand.role)} := by
  unfold compile at built ⊢
  unfold ordinarySource
  dsimp only
  cases found : GeneralSourceMetadataBuildRoles291.build p.metadata.sourceInput.roles with
  | none => simp [found] at built
  | some roles =>
    have eq := Option.some.inj (show
      some ⟨p.metadata.sourceInput.declared,p.metadata.sourceInput.snapshot,roles,p.metadata.sourceInput.declarations⟩ =
        some parent from by simpa only [found,Option.bind_some] using built)
    cases eq
    simp

theorem same_head_order (key : Nat) (x y : View) (left : x.box = key) (right : y.box = key) :
    DeclaredSubtype (table key) (GeneralDeclarativeWitnessCovariantViews353.View.head x)
      (GeneralDeclarativeWitnessCovariantViews353.View.head y) ↔ Common.Subtype x.payload y.payload := by
  constructor
  · intro measured
    obtain ⟨signature,chosen,_,supports⟩ := (declared_subtype_exact ..).mp measured
    change (table key)[x.box]? = some signature at chosen
    rw [left,table_key] at chosen
    cases Option.some.inj chosen
    exact supports.1.2.2
  · exact actual_box_order x y key left right

theorem current_is_join (key : Nat) (x y c upper : View)
    (l : x.box = key) (r : y.box = key) (host : c.box = key) (target : upper.box = key)
    (root : Common.Equivalent c.payload (.union x.payload y.payload)) :
    DeclaredSubtype (table key) (GeneralDeclarativeWitnessCovariantViews353.View.head c)
      (GeneralDeclarativeWitnessCovariantViews353.View.head upper) ↔
    DeclaredSubtype (table key) (GeneralDeclarativeWitnessCovariantViews353.View.head x)
      (GeneralDeclarativeWitnessCovariantViews353.View.head upper) ∧
    DeclaredSubtype (table key) (GeneralDeclarativeWitnessCovariantViews353.View.head y)
      (GeneralDeclarativeWitnessCovariantViews353.View.head upper) := by
  rw [same_head_order key c upper host target,same_head_order key x upper l target,
    same_head_order key y upper r target,← Common.common_union_is_join]
  exact ⟨Common.subtype_trans root.2,Common.subtype_trans root.1⟩

/-- Combine the typed declared head and the actual compiler subtree
without promoting the covariant root to C337's invariant nominal carrier. -/
theorem evidence {p : Problem} {e : Environment p} {s : State}
    {w : GeneralDeclarativeWitnessCovariantForest353.Wire} {report : Report}
    (a : Accepted p e s w report) (m : Assignment) (v : Valuation)
    (fit : Models s m) (actual : ∀ r ∈ p.rows, HasView m v r) :
    (∃ host : View, v a.head.prepared.anchor.arg.center = some host ∧
      host.tag = a.head.prepared.anchor.shape.tag ∧ host.box = w.head.box ∧
      Common.Equivalent host.payload
        (.union (GeneralDeclarativeWitnessCovariantOrigin353.assigned m a.head.prepared.anchor.first.valueName).1
                (GeneralDeclarativeWitnessCovariantOrigin353.assigned m a.head.prepared.anchor.last.valueName).1)) ∧
    (∀ pair ∈ a.head.prepared.ctx.spans,
      CommonNominalFullCarrier.Equivalent (m pair.2.center).1
        (.union (m a.head.prepared.anchor.first.valueName).1 (m a.head.prepared.anchor.last.valueName).1)) ∧
    All₂ (Evidence (registry a.ordinary) (interpretation a.ordinary.snapshot) m)
      a.head.receipt.compiled.kids a.children.entries ∧
    report.result = .selected (.node a.head.prepared.decl.id a.children.entries) ∧
    report.outputs = p.demand.outputs ∧
    ∀ e ∈ w.rootOut.outputRows,Holds m e := by
  obtain ⟨host,seen,tag,box,whole⟩ := GeneralDeclarativeWitnessCovariantOrigin353.actual_center
    a.head.prepared.anchor m v ⟨retained a.head m fit,actual⟩
  have proof := well_formed a m fit
  exact ⟨⟨host,seen,tag,box.trans a.head.prepared.anchor.sameBox,whole⟩,
    (confirmed a.head m fit).1,proof.2.2.2.1,proof.2.1,proof.2.2.1,proof.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantJoin353
