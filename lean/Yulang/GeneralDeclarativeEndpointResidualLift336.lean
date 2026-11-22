import Yulang.GeneralDeclarativeEndpointResidualReflect336
import Yulang.CommonNominalFullConstructors
import Yulang.GeneralDeclarativeEndpointNames336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointResidualLift336
open GeneralDeclarativeEndpointRecord336 (Read interp)
open GeneralDeclarativeEndpointResidual336 (exact_residuals)
open GeneralDeclarativeEndpointResidualReflect336 (reflect)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (ends)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonNominalFullCarrier (Ty Equivalent Subtype observeTy mask subtype_refl subtype_trans
  common_inter_is_meet common_union_is_join common_mask_idempotent)
open CommonNominalFullDemand (ProbeAt MaskedProbeAt MaskedProbeStep)

theorem mask_join (keys : List Nat) (a b : Ty) :
    Equivalent (mask keys (.union a b)) (.union (mask keys a) (mask keys b)) := by
  have semantic (d : Nat) :
      CommonNominalFullDemand.ProducerEq Common.rowLe
        (observeTy d (mask keys (.union a b))) (observeTy d (.union (mask keys a) (mask keys b))) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env obs
    change ProbeAt Common.rowLe rank env (.mask keys (.union (observeTy d a) (observeTy d b))) obs ↔
      ProbeAt Common.rowLe rank env (.union (.mask keys (observeTy d a)) (.mask keys (observeTy d b))) obs
    cases rank <;> cases obs <;> rfl
  exact ⟨fun d => (semantic d).1,fun d => (semantic d).2⟩

theorem mask_meet (keys : List Nat) (a b : Ty) :
    Equivalent (mask keys (.inter a b)) (.inter (mask keys a) (mask keys b)) := by
  have semantic (d : Nat) :
      CommonNominalFullDemand.ProducerEq Common.rowLe
        (observeTy d (mask keys (.inter a b))) (observeTy d (.inter (mask keys a) (mask keys b))) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env obs
    change ProbeAt Common.rowLe rank env (.mask keys (.inter (observeTy d a) (observeTy d b))) obs ↔
      ProbeAt Common.rowLe rank env (.inter (.mask keys (observeTy d a)) (.mask keys (observeTy d b))) obs
    cases rank <;> cases obs <;> rfl
  exact ⟨fun d => (semantic d).1,fun d => (semantic d).2⟩

def representative (keys : List Nat) (lo hi actual : Ty) : Ty :=
  .inter hi (.union lo (mask keys actual))

/-- This explicit representative lies in the *unmasked* source
interval and has exactly the projected observations. The theorem
does not identify it with a unique standalone type outside the
interval; it does not choose a language rule for erased observations. -/
theorem reifies (ordered : Subtype lo hi)
    (projected : InInterval (mask keys lo) (mask keys hi) (mask keys actual)) :
    InInterval lo hi (representative keys lo hi actual) ∧
      Equivalent (mask keys (representative keys lo hi actual)) (mask keys actual) := by
  let L := mask keys lo
  let H := mask keys hi
  let C := mask keys actual
  let CC := mask keys C
  have idem : Equivalent CC C := common_mask_idempotent actual keys
  have j : Equivalent (.union L CC) C := by
    refine ⟨(common_union_is_join _ _ _).mpr ⟨projected.1,idem.1⟩,?_⟩
    exact subtype_trans idem.2 ((common_union_is_join ..).mp (subtype_refl _)).2
  have k : Equivalent (.inter H (.union L CC)) C := by
    refine ⟨subtype_trans ((common_inter_is_meet ..).mp (subtype_refl _)).2 j.1,?_⟩
    exact (common_inter_is_meet ..).mpr ⟨projected.2,j.2⟩
  have literal : InInterval lo hi (representative keys lo hi actual) := by
    refine ⟨(common_inter_is_meet ..).mpr ⟨ordered,?_⟩,
      ((common_inter_is_meet ..).mp (subtype_refl _)).1⟩
    exact ((common_union_is_join ..).mp (subtype_refl _)).1
  refine ⟨literal,eqv_trans (mask_meet keys hi (.union lo C)) (eqv_trans ?_ k)⟩
  have expand := mask_join keys lo C
  exact ⟨(common_inter_is_meet ..).mpr ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
      subtype_trans ((common_inter_is_meet ..).mp (subtype_refl _)).2 expand.1⟩,
    (common_inter_is_meet ..).mpr ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
      subtype_trans ((common_inter_is_meet ..).mp (subtype_refl _)).2 expand.2⟩⟩

theorem residual_clear (keys : List Nat) (raw : Row Expr) :
    ∀ label ∈ keys, label ∉ (residual keys (normalize raw)).map Prod.fst := by
  intro label inKeys supposed
  obtain ⟨row,inRest,fst⟩ := List.mem_map.mp supposed
  exact ((CommonRoleCanonicalRows.mem_residual keys _ _).mp inRest).2 (fst ▸ inKeys)

theorem lifted {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m) (fit : Models s m) :
    let lo := interp m (withTail (residual keys (normalize ls)) le)
    let hi := interp m (withTail (residual keys (normalize us)) ue)
    let actual := (m arg.center).1
    ∃ val, InInterval lo hi val ∧ Equivalent (mask keys val) (mask keys actual) := by
  dsimp only
  have projected := exact_residuals r m fit
  have order := reflect m keys _ _ (ends r.lo) (ends r.hi) (residual_clear keys ls) (residual_clear keys us)
    (subtype_trans projected.1 projected.2)
  exact ⟨_,reifies order projected⟩

/-- Standalone typed residuals can be named conservatively before
I-58 or output writes. This certifies a reified representative, not
complete operational assignment of an opaque principal residual. -/
theorem named {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m) (fit : Models s m) (keep : List Nat) :
    let lo := interp m (withTail (residual keys (normalize ls)) le)
    let hi := interp m (withTail (residual keys (normalize us)) ue)
    let fresh := GeneralDeclarativeEndpointNames336.names s (arg.center :: keep)
    ∃ picked,
      Models (GeneralDeclarativeEndpointNames336.prepare s (arg.center :: keep)) picked ∧
      (∀ x ∈ GeneralDeclarativeEndpointNames336.prior s (arg.center :: keep), picked x = m x) ∧
      (picked fresh.lower).1 = lo ∧ (picked fresh.upper).1 = hi ∧
      Equivalent (mask keys (picked fresh.center).1) (mask keys (picked arg.center).1) := by
  dsimp only
  let lo := interp m (withTail (residual keys (normalize ls)) le)
  let hi := interp m (withTail (residual keys (normalize us)) ue)
  obtain ⟨mid,inside,agrees⟩ := lifted r m fit
  let vals : GeneralDeclarativeEndpointNames336.Triple := (lo,mid,hi)
  let next := GeneralDeclarativeEndpointNames336.extend s (arg.center :: keep) m vals
  obtain ⟨model,old⟩ := GeneralDeclarativeEndpointNames336.extension (v := vals) fit inside (arg.center :: keep)
  have present := GeneralDeclarativeEndpointNames336.values s (arg.center :: keep) m vals
  have before := old arg.center (List.mem_append_right _ List.mem_cons_self)
  refine ⟨next,model,old,congrArg Prod.fst present,congrArg
    (fun z : GeneralDeclarativeEndpointNames336.Triple => z.2.2) present,?_⟩
  have center := congrArg (fun z : GeneralDeclarativeEndpointNames336.Triple => z.2.1) present
  change (next (GeneralDeclarativeEndpointNames336.names s (arg.center :: keep)).center).1 = mid at center
  have actual : next arg.center = m arg.center := before
  rw [center,actual]
  exact agrees

/-- Any two candidates in a point residual interval agree as
standalone types, even when their masked type is weaker. -/
theorem point_unique {lo hi a b : Ty} (point : Subtype hi lo)
    (first : InInterval lo hi a) (second : InInterval lo hi b) : Equivalent a b :=
  ⟨subtype_trans first.2 (subtype_trans point second.1),
    subtype_trans second.2 (subtype_trans point first.1)⟩

theorem rigid_unique (m) (keys : List Nat) (ls us : Row Expr)
    (lo : GeneralDeclarativeRecordSpine330.Terminal le) (hi : GeneralDeclarativeRecordSpine330.Terminal ue)
    (low : ∀ k ∈ keys, k ∉ ls.map Prod.fst) (high : ∀ k ∈ keys, k ∉ us.map Prod.fst)
    (same : Equivalent (mask keys (interp m (withTail ls le))) (mask keys (interp m (withTail us ue)))) :
    Equivalent (interp m (withTail ls le)) (interp m (withTail us ue)) :=
  ⟨reflect m keys ls us lo hi low high same.1,reflect m keys us ls hi lo high low same.2⟩

open CommonNominalFullCarrier (exactEmpty emptyRecord exactEmpty_below_width)
open CommonNominalFullDemand (ProbeStep)

theorem exact_below_forgetting (keys : List Nat) : Subtype exactEmpty (mask keys exactEmpty) := by
  intro d
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;> simp_all [observeTy,exactEmpty,mask,ProbeAt,ProbeStep,MaskedProbeStep,
    CommonNominalSyntax.Layer.evalAt]

theorem forgetting_below_open (keys : List Nat) : Subtype (mask keys exactEmpty) emptyRecord := by
  have openKnown := GeneralDeclarativeEndpointResidualSemantics336.open_disjoint
    (fun _ => (.bottom,Common.rowEmpty)) keys [] (fun _ _ h => List.not_mem_nil h)
  exact subtype_trans (GeneralDeclarativeEndpointRecord336.mask_below keys exactEmpty_below_width) openKnown.1

/-- Model precise nonuniqueness when a closed lower and open upper
bound are different. Observable removed-label absence cannot be
recovered solely from masked observations and these bounds. This is
a representation counterexample, not a language acceptance claim. -/
theorem nonunique (keys : List Nat) (label : Nat) (removed : label ∈ keys) :
    InInterval exactEmpty emptyRecord exactEmpty ∧
    InInterval exactEmpty emptyRecord (mask keys exactEmpty) ∧
    Equivalent (mask keys (mask keys exactEmpty)) (mask keys exactEmpty) ∧
    ¬ Equivalent (mask keys exactEmpty) exactEmpty :=
  ⟨⟨subtype_refl _,exactEmpty_below_width⟩,⟨exact_below_forgetting keys,forgetting_below_open keys⟩,
    common_mask_idempotent _ keys,fun h =>
      GeneralDeclarativeEndpointResidualSemantics336.closed_distinct keys label removed h.1⟩


end Yulang.GeneralDeclarativeEndpointResidualLift336
