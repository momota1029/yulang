import Yulang.CommonGeneratedRigidPool
import Yulang.CommonSymbolicRigidInspection
import Yulang.CommonSymbolicSourceProfiles

/-!
# Symbolic discharge of every actual generated rigid endpoint

`saturate` consumes only the actual shared source pool and its finite edge
list. It does not receive rows, values, an interpreter, fuel or a solver
certificate. Original variable-bound propagation has already produced rigid
endpoints. The generated-endpoint theorem proves, internally for every source
and Core clause, which endpoint cases can arise after scheme instantiation,
normalization, packing and that propagation.

Every input rigid comparison is decomposed into original child IDs, symbolic
row comparisons and finite record profile / presence expressions. Known
record and default heads are expanded before substitution; only queries of
unknown shared nodes remain primitive. Static failures produce no branch.
There is no atom for the original whole rigid subtype comparison.

This is the first-pass contract `saturate_common_rigid_exact`, under the
independent constructor equations and for all row/value assignments. Closing
the new child/profile/row constraints under repeated propagation is the next
contract. In particular a negative arrow child can reverse the original
endpoint polarity; the original endpoint invariant alone is not a proof of
that recursive closure or of all-parameter solver soundness.
-/

namespace Yulang.CommonGeneratedRigidInspection

open Common (Ty Row Equivalent Subtype)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (lowerNode rowEval Realizes EdgesHold splitAtoms compile)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonSymbolicRecordProfiles (BoolExpr)
open CommonPayloadProjection (Payload)
open CommonSymbolicSourceProfiles (compileNode)
open PresenceGeneratedRigidShape (lower upper)

variable {m : Nat}

abbrev Checks (pool : Pool m) := Branch (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size)
abbrev RigidNode (pool : Pool m) := CommonSymbolicRigidInspection.Node (RowTerm (Fin m)) (Fin pool.size)

private theorem subtype_congr {first first' last last' : Ty}
    (source : Equivalent first first') (target : Equivalent last last') :
    Subtype first last ↔ Subtype first' last' :=
  ⟨fun below => Common.subtype_trans source.2 (Common.subtype_trans below target.1),
    fun below => Common.subtype_trans source.1 (Common.subtype_trans below target.2)⟩

private theorem target_congr (source : Ty) {target actual : Ty} (same : Equivalent target actual) :
    Subtype source actual ↔ Subtype source target :=
  ⟨fun below => Common.subtype_trans below same.2,
    fun below => Common.subtype_trans below same.1⟩

/-- Non-record target inspection. A source union emits two proper-child
comparisons; all other supported rigid cases use the independent inspector. -/
def inspectSource (pool : Pool m) (source : TyTerm (Fin m)) (member : source ∈ pool.terms)
    (target : RigidNode pool) (targetSlot : Fin pool.size) : Checks pool :=
  match source with
  | .var index => [.childBelow (.ref (pool.input index)) (.ref targetSlot)]
  | .union first last => CommonSymbolicRigidInspection.unionLeft
      (pool.child _ member first (by simp [subterms]))
      (pool.child _ member last (by simp [subterms])) targetSlot
  | .inter _ _ => [.flag (.literal false)]
  | .bottom => CommonSymbolicRigidInspection.inspect .bottom target
  | .top => CommonSymbolicRigidInspection.inspect .top target
  | .base scalar => CommonSymbolicRigidInspection.inspect (.base scalar) target
  | .pair first last => CommonSymbolicRigidInspection.inspect
      (.pair (pool.child _ member first (by simp [subterms]))
        (pool.child _ member last (by simp [subterms]))) target
  | .variant label payload => CommonSymbolicRigidInspection.inspect
      (.variant label (pool.child _ member payload (by simp [subterms]))) target
  | .arrow input incoming output outgoing => CommonSymbolicRigidInspection.inspect
      (.arrow (pool.child _ member input (by simp [subterms])) incoming
        (pool.child _ member output (by simp [subterms])) outgoing) target
  | .emptyRecord | .exactEmpty | .required _ _ | .record _ _ _ | .recordDefault _ _ _ =>
      match target with
      | .top => []
      | _ => [.flag (.literal false)]

theorem inspectSource_exact (pool : Pool m) (source : TyTerm (Fin m)) (member : source ∈ pool.terms)
    (target : RigidNode pool) (targetSlot : Fin pool.size) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (targetSame : Equivalent (target.eval (rowEval rows) values) (values targetSlot))
    (sourceShape : lower source = true) :
    Branch.Holds (rowEval rows) values values (inspectSource pool source member target targetSlot) ↔
      Subtype ((lowerNode pool source member).eval rows values) (target.eval (rowEval rows) values) := by
  cases source with
  | var index =>
      simp only [inspectSource, CommonSymbolicConstraints.holds_cons, CommonSymbolicConstraints.holds_nil,
        Check.Holds, Payload.evalLayer, and_true, lowerNode, CommonRowTailInference.Body.eval]
      exact target_congr _ targetSame
  | union first last =>
      rw [inspectSource, CommonSymbolicRigidInspection.union_left_exact]
      exact target_congr _ targetSame
  | inter => cases sourceShape
  | bottom => exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values .bottom target
  | top => exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values .top target
  | base scalar => exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values (.base scalar) target
  | pair first last =>
      exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values
        (.pair (pool.child _ member first (by simp [subterms]))
          (pool.child _ member last (by simp [subterms]))) target
  | variant label payload =>
      exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values
        (.variant label (pool.child _ member payload (by simp [subterms]))) target
  | arrow input incoming output outgoing =>
      exact CommonSymbolicRigidInspection.inspect_exact (rowEval rows) values values
        (.arrow (pool.child _ member input (by simp [subterms])) incoming
          (pool.child _ member output (by simp [subterms])) outgoing) target
  | emptyRecord | exactEmpty | required _ _ | record _ _ _ | recordDefault _ _ _ =>
      cases target
      all_goals simp only [inspectSource, CommonSymbolicConstraints.holds_cons,
        CommonSymbolicConstraints.holds_nil, Check.Holds, BoolExpr.eval, Bool.false_eq_true,
        and_true, CommonSymbolicRigidInspection.Node.eval]
      all_goals try exact (iff_true_intro (CommonBoundCoalescing.le_top _)).symm
      all_goals
        exact (iff_false_intro (CommonRigidHeadInspection.rigid_mismatch rfl rfl
          (by simp [CommonRigidHeadInspection.head, lowerNode, CommonRowTailInference.Body.eval,
            CommonRowTailInference.layerAtRows, CommonPresenceTailLayers.quoteLayer,
            CommonSyntax.Layer.map, Common.record, Common.recordDefault])
          (by simp [CommonRigidHeadInspection.head, Common.pair, Common.arrow, Common.variant])
          (by simp [CommonRigidHeadInspection.head, lowerNode, CommonRowTailInference.Body.eval,
            CommonRowTailInference.layerAtRows, CommonPresenceTailLayers.quoteLayer,
            CommonSyntax.Layer.map, Common.record,
            Common.recordDefault, Common.pair, Common.arrow, Common.variant]))).symm

/-- The construction is total finite syntax traversal. Unsupported endpoint
shapes cannot occur in the generated first-pass theorem below. -/
def inspect (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms) : Checks pool :=
  match target with
  | .var index => [.childBelow (.ref (pool.reference source sourceMember)) (.ref (pool.input index))]
  | .emptyRecord => [.flag (compileNode pool [] 0 source sourceMember).records]
  | .required label payload =>
      [.profileBelow (compileNode pool [] label source sourceMember).field
        (.ref (pool.child _ targetMember payload (by simp [subterms])))]
  | .base scalar => inspectSource pool source sourceMember (.base scalar) (pool.reference _ targetMember)
  | .pair first last => inspectSource pool source sourceMember
      (.pair (pool.child _ targetMember first (by simp [subterms]))
        (pool.child _ targetMember last (by simp [subterms]))) (pool.reference _ targetMember)
  | .arrow input incoming output outgoing => inspectSource pool source sourceMember
      (.arrow (pool.child _ targetMember input (by simp [subterms])) incoming
        (pool.child _ targetMember output (by simp [subterms])) outgoing) (pool.reference _ targetMember)
  | .bottom => inspectSource pool source sourceMember .bottom (pool.reference _ targetMember)
  | .top => []
  | .variant label payload => inspectSource pool source sourceMember
      (.variant label (pool.child _ targetMember payload (by simp [subterms]))) (pool.reference _ targetMember)
  | .inter first last => CommonSymbolicRigidInspection.interRight (pool.reference source sourceMember)
      (pool.child _ targetMember first (by simp [subterms]))
      (pool.child _ targetMember last (by simp [subterms]))
  | _ => [.flag (.literal false)]

/-- The independent original constructor equations suffice. Neither source
typing nor a particular equation solver's output is a premise. -/
theorem inspect_exact (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (sourceShape : lower source = true) (targetShape : upper target = true)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Branch.Holds (rowEval rows) values values (inspect pool source target sourceMember targetMember) ↔
      Subtype (values (pool.reference source sourceMember)) (values (pool.reference target targetMember)) := by
  have sourceSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes source sourceMember
  have targetSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes target targetMember
  cases target with
  | var index => simp [inspect, Branch.Holds, Check.Holds, Payload.evalLayer, Pool.input]
  | emptyRecord =>
      simpa only [inspect, CommonSymbolicConstraints.holds_cons, CommonSymbolicConstraints.holds_nil,
        Check.Holds, and_true] using
        (CommonSymbolicSourceProfiles.node_emptyRecord_exact pool source sourceMember rows values).symm.trans
          (subtype_congr sourceSame targetSame)
  | required label payload =>
      simpa only [inspect, CommonSymbolicConstraints.holds_cons, CommonSymbolicConstraints.holds_nil,
        Check.Holds, and_true] using
        (CommonSymbolicSourceProfiles.node_required_exact pool source sourceMember rows values label
          (.ref (pool.child _ targetMember payload (by simp [subterms])))).symm.trans
          (subtype_congr sourceSame targetSame)
  | base scalar =>
      exact (inspectSource_exact pool source sourceMember (.base scalar)
        (pool.reference _ targetMember) rows values targetSame sourceShape).trans
          (subtype_congr sourceSame targetSame)
  | pair first last =>
      exact (inspectSource_exact pool source sourceMember
        (.pair (pool.child _ targetMember first (by simp [subterms]))
          (pool.child _ targetMember last (by simp [subterms])))
        (pool.reference _ targetMember) rows values targetSame sourceShape).trans
          (subtype_congr sourceSame targetSame)
  | arrow input incoming output outgoing =>
      exact (inspectSource_exact pool source sourceMember
        (.arrow (pool.child _ targetMember input (by simp [subterms])) incoming
          (pool.child _ targetMember output (by simp [subterms])) outgoing)
        (pool.reference _ targetMember) rows values targetSame sourceShape).trans
          (subtype_congr sourceSame targetSame)
  | _ => cases targetShape

def inspectSlot (pool : Pool m) (edge : Fin pool.size × Fin pool.size) : Checks pool :=
  inspect pool (pool.termAt edge.1) (pool.termAt edge.2) (pool.at_mem edge.1) (pool.at_mem edge.2)

theorem inspect_slot_exact (pool : Pool m) (edge : Fin pool.size × Fin pool.size)
    (sourceShape : lower (pool.termAt edge.1) = true) (targetShape : upper (pool.termAt edge.2) = true)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Branch.Holds (rowEval rows) values values (inspectSlot pool edge) ↔
      Subtype (values edge.1) (values edge.2) := by
  simpa only [Pool.reference_termAt, inspectSlot] using
    inspect_exact pool _ _ _ _ sourceShape targetShape rows values realizes

/-- Only finite source syntax and original IDs are inputs. All parameter
assignments are supplied to the independent meaning, never to this function. -/
def saturate (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) :
    Alternatives (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) :=
  CommonSymbolicConstraints.discharge (edges.flatMap (inspectSlot pool))

theorem saturate_exact (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (shapes : CommonGeneratedRigidPool.EndpointShapes pool edges)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Alternatives.Holds (rowEval rows) values values (saturate pool edges) ↔ EdgesHold edges values := by
  rw [saturate, CommonSymbolicConstraints.discharge_exact, CommonSymbolicConstraints.holds_flatMap]
  constructor
  · intro inspected edge member
    exact (inspect_slot_exact pool edge (shapes edge member).1 (shapes edge member).2 rows values realizes).mp
      (inspected edge member)
  · intro valid edge member
    exact (inspect_slot_exact pool edge (shapes edge member).1 (shapes edge member).2 rows values realizes).mpr
      (valid edge member)

/-- Contract 7.1 for every actual generated packed source clause, arbitrary
independent rows/values, and the original constructor equations. The endpoint
grammar is proved from generation, not supplied as a public support premise. -/
theorem saturate_common_rigid_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values) :
    EdgesHold (CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges)) values ↔
      ∃ branch ∈ saturate (splitAtoms clause.pack).pool
        (CommonBoundCoalescing.rigidComparisons
          (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges)),
        Branch.Holds (rowEval rows) values values branch :=
  (saturate_exact _ _ (CommonGeneratedRigidPool.generated_residual_endpoint_shapes expression clause member)
    rows values realizes).symm

theorem saturate_common_core_rigid_exact (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values) :
    EdgesHold (CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges)) values ↔
      ∃ branch ∈ saturate (splitAtoms clause.pack).pool
        (CommonBoundCoalescing.rigidComparisons
          (CommonPresenceVariableBounds.template (splitAtoms clause.pack).pool (compile clause.pack).edges)),
        Branch.Holds (rowEval rows) values values branch :=
  (saturate_exact _ _ (CommonGeneratedRigidPool.generated_core_residual_endpoint_shapes expression clause member)
    rows values realizes).symm

end Yulang.CommonGeneratedRigidInspection
