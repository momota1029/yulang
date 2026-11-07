import Yulang.CommonSymbolicBoundInspection

/-!
# Non-record inspection with the same fixed bound references

The existing rigid inspector is reused with `BoundRef` children. A source
union emits two edges to the same target reference; reference/target meaning
agreement is an explicit independent equivalence premise. Known record
heads are rejected by role observations, except for the top target.
-/

namespace Yulang.CommonSymbolicBoundInspection

open Common (Ty Row Subtype Equivalent)
open CommonSymbolicConstraints (Check)

def inspectRigid (source : Source Rows Node) (target : Rigid Rows Node)
    (targetRef : BoundRef Node) : Output Rows Node :=
  match source with
  | .reference node => [[edge node targetRef]]
  | .union first last => [[edge first targetRef, edge last targetRef]]
  | .rigid node => [CommonSymbolicRigidInspection.inspect node target]
  | _ => match target with
    | .top => [[]]
    | _ => []

theorem target_congr (source : Ty) {target actual : Ty} (same : Equivalent target actual) :
    Subtype source actual ↔ Subtype source target :=
  ⟨fun below => Common.subtype_trans below same.2,
    fun below => Common.subtype_trans below same.1⟩

theorem subtype_congr {source source' target target' : Ty}
    (first : Equivalent source source') (last : Equivalent target target') :
    Subtype source target ↔ Subtype source' target' :=
  ⟨fun below => Common.subtype_trans first.2 (Common.subtype_trans below last.1),
    fun below => Common.subtype_trans first.1 (Common.subtype_trans below last.2)⟩

theorem inspect_rigid_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (target : Rigid Rows Node) (targetRef : BoundRef Node)
    (targetSame : Equivalent (target.eval rows (BoundRef.eval values)) (targetRef.eval values)) :
    Holds rows values (inspectRigid source target targetRef) ↔
      Subtype (source.eval rows values) (target.eval rows (BoundRef.eval values)) := by
  cases source with
  | reference node =>
      rw [inspectRigid, holds_edge]
      exact target_congr _ targetSame
  | union first last =>
      rw [inspectRigid, holds_two]
      exact (Common.common_union_is_join _ _ _).symm.trans (target_congr _ targetSame)
  | rigid node =>
      simpa only [inspectRigid, Holds, CommonSymbolicConstraints.alternatives_singleton,
        Source.eval] using
        CommonSymbolicRigidInspection.inspect_exact rows values (BoundRef.eval values) node target
  | width | exactEmpty | record | recordDefault =>
      cases target
      all_goals simp only [inspectRigid, holds_empty, holds_success, false_iff, true_iff,
        Source.eval, CommonSymbolicRigidInspection.Node.eval]
      all_goals try exact CommonBoundCoalescing.le_top _
      all_goals
        exact CommonRigidHeadInspection.rigid_mismatch rfl rfl
          (by simp [CommonRigidHeadInspection.head, Common.record, Common.recordDefault,
            Common.emptyRecord, Common.exactEmpty])
          (by simp [CommonRigidHeadInspection.head, Common.pair, Common.arrow, Common.variant])
          (by simp [CommonRigidHeadInspection.head, Common.record, Common.recordDefault,
            Common.emptyRecord, Common.exactEmpty, Common.pair, Common.arrow, Common.variant])

theorem inspect_rigid_plain (source : Source Rows Node) (target : Rigid Rows Node)
    (targetRef : BoundRef Node) : Plain (inspectRigid source target targetRef) := by
  cases source with
  | reference | union => simp [inspectRigid, Plain, edge, PlainCheck]
  | rigid node =>
      cases node <;> cases target <;>
        simp [inspectRigid, CommonSymbolicRigidInspection.inspect, Plain, PlainCheck]
  | width | exactEmpty | record | recordDefault =>
      cases target <;> simp [inspectRigid, Plain]

end Yulang.CommonSymbolicBoundInspection
