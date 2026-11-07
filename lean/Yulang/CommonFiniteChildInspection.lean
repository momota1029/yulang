import Yulang.CommonGeneratedChildClosure

/-!
# Finite-observation soundness of generated rigid inspection

Guarded pair/arrow payload comparisons use one smaller constructor observation.
Source-union comparisons stay at the same observation and use proper source
children. Row, Boolean and record-profile constraints retain their independent
full meanings. This is the finite interface needed by a simultaneous depth and
source-syntax induction; it does not assume the child comparisons at all depths.
-/

namespace Yulang.CommonFiniteChildInspection

open Common (Ty Row)
open CommonSymbolicConstraints (Check Branch)
open CommonPayloadProjection (Payload)
open CommonSymbolicRigidInspection (Node)

def BelowAt (depth : Nat) (source target : Ty) : Prop :=
  CommonFinite.ProducerLe Common.rowLe (Common.observeTy depth source) (Common.observeTy depth target)

def GuardedAt (depth : Nat) (source target : Ty) : Prop :=
  CommonFinite.ProducerLe Common.rowLe
    (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node source))
    (CommonSyntax.observe (CommonSyntax.graph Row) depth (.node target))

@[simp] theorem guarded_zero (source target : Ty) : GuardedAt 0 source target :=
  CommonFinite.producerLe_refl _

@[simp] theorem guarded_succ (depth : Nat) (source target : Ty) :
    GuardedAt (depth + 1) source target ↔ BelowAt depth source target := Iff.rfl

def CheckAt (sameDepth : Bool) (depth : Nat) (rows : Rows → Row)
    (nodes : NodeIndex → Ty) (children : Child → Ty) : Check Rows NodeIndex Child → Prop
  | .childBelow source target =>
      if sameDepth then BelowAt depth (source.evalLayer children) (target.evalLayer children)
      else GuardedAt depth (source.evalLayer children) (target.evalLayer children)
  | other => other.Holds rows nodes children

def BranchAt (sameDepth : Bool) (depth : Nat) (rows : Rows → Row)
    (nodes : NodeIndex → Ty) (children : Child → Ty) (checks : Branch Rows NodeIndex Child) : Prop :=
  ∀ check ∈ checks, CheckAt sameDepth depth rows nodes children check

@[simp] theorem branchAt_nil (sameDepth : Bool) (depth : Nat) (rows : Rows → Row)
    (nodes : NodeIndex → Ty) (children : Child → Ty) : BranchAt sameDepth depth rows nodes children [] := by
  simp [BranchAt]

@[simp] theorem branchAt_cons (sameDepth : Bool) (depth : Nat) (rows : Rows → Row)
    (nodes : NodeIndex → Ty) (children : Child → Ty) (check : Check Rows NodeIndex Child)
    (rest : Branch Rows NodeIndex Child) :
    BranchAt sameDepth depth rows nodes children (check :: rest) ↔
      CheckAt sameDepth depth rows nodes children check ∧ BranchAt sameDepth depth rows nodes children rest := by
  simp only [BranchAt, List.mem_cons, forall_eq_or_imp]

theorem node_inspect_at_sound (depth : Nat) (rows : Rows → Row) (nodes : NodeIndex → Ty)
    (children : Child → Ty) (source target : Node Rows Child)
    (valid : BranchAt false depth rows nodes children (CommonSymbolicRigidInspection.inspect source target)) :
    BelowAt depth (source.eval rows children) (target.eval rows children) := by
  cases source <;> cases target
  all_goals simp only [CommonSymbolicRigidInspection.inspect, branchAt_nil, branchAt_cons, CheckAt,
    Check.Holds, CommonSymbolicRecordProfiles.BoolExpr.eval, Bool.false_eq_true,
    decide_eq_true_eq, and_true, Bool.false_eq_true, ↓reduceIte, Payload.evalLayer] at valid
  all_goals try contradiction
  all_goals try exact CommonBoundCoalescing.bottom_le _ depth
  all_goals try exact CommonBoundCoalescing.le_top _ depth
  case base.base first last =>
    cases valid
    exact CommonFinite.producerLe_refl _
  case pair.pair => exact (CommonFinite.producerLe_pair_iff _ _ _ _).mpr valid
  case arrow.arrow => exact (CommonFinite.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans _ _ _ _ _ _ _ _).mpr valid
  case variant.variant first payload last payload' =>
    rcases valid with ⟨rfl, valid⟩
    exact (CommonFinite.producerLe_variant_iff first _ _).mpr valid

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonGeneratedRigidInspection (inspect inspectSource inspectSlot RigidNode)
open CommonPresenceConstraintGraph (rowEval lowerNode Realizes)
open PresenceGeneratedChildGrammar (lower upper)
open CommonGeneratedRigidDescent (rigid)

variable {m : Nat}

def sameDepth : TyTerm α → Bool
  | .union _ _ => true
  | _ => false

private theorem belowAt_congr (depth : Nat) {source source' target target' : Ty}
    (first : Common.Equivalent source source') (last : Common.Equivalent target target') :
    BelowAt depth source target ↔ BelowAt depth source' target' :=
  ⟨fun below => CommonFinite.producerLe_trans (first.2 depth)
      (CommonFinite.producerLe_trans below (last.1 depth)),
    fun below => CommonFinite.producerLe_trans (first.1 depth)
      (CommonFinite.producerLe_trans below (last.2 depth))⟩

theorem inspectSource_at_sound (depth : Nat) (pool : Pool m) (source : TyTerm (Fin m))
    (member : source ∈ pool.terms) (target : RigidNode pool) (targetSlot : Fin pool.size)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (targetSame : Common.Equivalent (target.eval (rowEval rows) values) (values targetSlot))
    (sourceGrammar : lower source = true) (sourceRigid : rigid source)
    (valid : BranchAt (sameDepth source) depth (rowEval rows) values values
      (inspectSource pool source member target targetSlot)) :
    BelowAt depth ((lowerNode pool source member).eval rows values) (target.eval (rowEval rows) values) := by
  cases source with
  | var => cases sourceRigid
  | inter => cases sourceGrammar
  | union first last =>
      simp only [sameDepth, inspectSource, CommonSymbolicRigidInspection.unionLeft,
        branchAt_cons, branchAt_nil, CheckAt, ↓reduceIte, Payload.evalLayer, and_true] at valid
      exact CommonFinite.producerLe_trans ((CommonFinite.producerLe_union_iff _ _ _).mpr valid)
        (targetSame.2 depth)
  | bottom => exact node_inspect_at_sound depth (rowEval rows) values values .bottom target valid
  | top => exact node_inspect_at_sound depth (rowEval rows) values values .top target valid
  | base scalar => exact node_inspect_at_sound depth (rowEval rows) values values (.base scalar) target valid
  | pair first last =>
      exact node_inspect_at_sound depth (rowEval rows) values values
        (.pair (pool.child _ member first (by simp [subterms]))
          (pool.child _ member last (by simp [subterms]))) target valid
  | variant label payload =>
      exact node_inspect_at_sound depth (rowEval rows) values values
        (.variant label (pool.child _ member payload (by simp [subterms]))) target valid
  | arrow input incoming output outgoing =>
      exact node_inspect_at_sound depth (rowEval rows) values values
        (.arrow (pool.child _ member input (by simp [subterms])) incoming
          (pool.child _ member output (by simp [subterms])) outgoing) target valid
  | emptyRecord | exactEmpty | required _ _ | record _ _ _ | recordDefault _ _ _ =>
      cases target
      all_goals simp only [inspectSource, branchAt_cons, branchAt_nil, CheckAt, Check.Holds,
        CommonSymbolicRecordProfiles.BoolExpr.eval, Bool.false_eq_true, and_true] at valid
      all_goals try contradiction
      all_goals exact CommonBoundCoalescing.le_top _ depth

/-- At a rigid generated endpoint, every same-depth child comes from source
union and every other ordinary child is guarded. Profile checks are explicit
independent hypotheses rather than assumed finite-shape approximations. -/
theorem inspect_at_sound (depth : Nat) (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (sourceGrammar : lower source = true) (targetGrammar : upper target = true)
    (sourceRigid : rigid source) (targetRigid : rigid target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (valid : BranchAt (sameDepth source) depth (rowEval rows) values values
      (inspect pool source target sourceMember targetMember)) :
    BelowAt depth (values (pool.reference source sourceMember)) (values (pool.reference target targetMember)) := by
  have sourceSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes source sourceMember
  have targetSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes target targetMember
  cases target with
  | var => cases targetRigid
  | emptyRecord | required _ _ =>
      apply (CommonGeneratedRigidInspection.inspect_exact pool source _ sourceMember targetMember
        (PresenceGeneratedChildGrammar.lower_head _ sourceGrammar)
        (PresenceGeneratedChildGrammar.upper_head _ targetGrammar) rows values realizes).mp ?_ depth
      simpa only [inspect, branchAt_cons, branchAt_nil, CommonSymbolicConstraints.holds_cons,
        CommonSymbolicConstraints.holds_nil, CheckAt, and_true] using valid
  | base scalar =>
      exact (belowAt_congr depth sourceSame targetSame).mp
        (inspectSource_at_sound depth pool source sourceMember (.base scalar) (pool.reference _ targetMember)
          rows values targetSame sourceGrammar sourceRigid valid)
  | pair first last =>
      exact (belowAt_congr depth sourceSame targetSame).mp
        (inspectSource_at_sound depth pool source sourceMember
          (.pair (pool.child _ targetMember first (by simp [subterms]))
            (pool.child _ targetMember last (by simp [subterms]))) (pool.reference _ targetMember)
          rows values targetSame sourceGrammar sourceRigid valid)
  | arrow input incoming output outgoing =>
      exact (belowAt_congr depth sourceSame targetSame).mp
        (inspectSource_at_sound depth pool source sourceMember
          (.arrow (pool.child _ targetMember input (by simp [subterms])) incoming
            (pool.child _ targetMember output (by simp [subterms])) outgoing) (pool.reference _ targetMember)
          rows values targetSame sourceGrammar sourceRigid valid)
  | _ => cases targetGrammar

theorem inspectSlot_at_sound (depth : Nat) (pool : Pool m) (edge : Fin pool.size × Fin pool.size)
    (sourceGrammar : lower (pool.termAt edge.1) = true) (targetGrammar : upper (pool.termAt edge.2) = true)
    (sourceRigid : rigid (pool.termAt edge.1)) (targetRigid : rigid (pool.termAt edge.2))
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (valid : BranchAt (sameDepth (pool.termAt edge.1)) depth (rowEval rows) values values (inspectSlot pool edge)) :
    BelowAt depth (values edge.1) (values edge.2) := by
  simpa only [Pool.reference_termAt] using inspect_at_sound depth pool _ _ _ _ sourceGrammar targetGrammar
    sourceRigid targetRigid rows values realizes valid

theorem sameDepth_child_decreases (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (targetGrammar : upper target = true) (targetRigid : rigid target)
    (isUnion : sameDepth source = true) (first last : Fin pool.size)
    (present : .childBelow (.ref first) (.ref last) ∈ inspect pool source target sourceMember targetMember) :
    CommonGeneratedRigidDescent.weight (pool.termAt first) < CommonGeneratedRigidDescent.weight source := by
  cases source <;> cases target
  all_goals simp_all [sameDepth, upper, rigid, inspect, inspectSource, CommonSymbolicRigidInspection.unionLeft]
  all_goals rcases present with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [Pool.child, Pool.termAt_reference, CommonGeneratedRigidDescent.weight]
  all_goals omega

end Yulang.CommonFiniteChildInspection
