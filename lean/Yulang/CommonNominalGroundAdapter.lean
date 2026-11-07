import Yulang.CommonNominalCarrier
import Yulang.CommonGroundNominalCasts

/-!
# Preserving the concrete ground adapter in the nested nominal carrier

The source grammar and normalization are the existing computed scalar/nominal
adapter. Its finite checker is retained verbatim. This module interprets that
same grammar in the new carrier whose arguments can also contain regular
nominals. No external compatibility oracle is assumed.
-/

namespace Yulang.CommonNominalGroundAdapter

open CommonNominalCarrier
open CommonGroundScalarCasts (Scalar)

private def finiteScalar : Scalar → CommonNominalFinite.Ty Row
  | .atom (.var index) => nomatch index
  | .atom (.base scalar) => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (finiteScalar first) (finiteScalar last)
  | .inter first last => .inter (finiteScalar first) (finiteScalar last)

def scalarMeaning : Scalar → Ty
  | .atom (.var index) => nomatch index
  | .atom (.base scalar) => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (scalarMeaning first) (scalarMeaning last)
  | .inter first last => .inter (scalarMeaning first) (scalarMeaning last)

private theorem observe_scalar (depth : Nat) (scalar : Scalar) :
    observeTy depth (scalarMeaning scalar) = finiteScalar scalar := by
  induction scalar with
  | atom atom => cases atom with
      | var index => exact Fin.elim0 index
      | base scalar => rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [scalarMeaning, finiteScalar, observeTy, CommonNominalSyntax.Layer.evalAt] at *
      rw [ihf, ihl]

private def oldObservation : CommonNominalFinite.Observation Row → CommonFinite.Observation Row
  | .trivial => .trivial
  | .base scalar => .base scalar
  | .role name => .role name
  | _ => .impossible

private def newObservation : CommonFinite.Observation Row → CommonNominalFinite.Observation Row
  | .trivial => .trivial
  | .base scalar => .base scalar
  | .role name => .role name
  | _ => .impossible

private theorem new_probe_old (rank : Nat) (env : CommonNominalFinite.Environment Row)
    (obs : CommonNominalFinite.Observation Row) (scalar : Scalar) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env (finiteScalar scalar) obs ↔
      CommonFinite.ProbeAt Common.rowLe rank ⟨fun _ => .bottom, env.roles⟩
        (CommonCanonicalOpen.finiteInstantiate Fin.elim0 scalar) (oldObservation obs) := by
  induction scalar with
  | atom atom => cases atom with
      | var index => exact Fin.elim0 index
      | base scalar =>
          cases rank <;> cases obs <;>
            simp [finiteScalar, oldObservation, CommonCanonicalOpen.finiteInstantiate,
              CommonCanonicalOpen.finiteAtom, CommonNominalFinite.ProbeAt,
              CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep,
              CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  | bottom | top =>
      cases rank <;> cases obs <;>
        simp [finiteScalar, oldObservation, CommonCanonicalOpen.finiteInstantiate,
          CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
          CommonNominalFinite.MaskedProbeStep, CommonFinite.ProbeAt,
          CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  | union first last ihf ihl | inter first last ihf ihl =>
      simp [finiteScalar, CommonCanonicalOpen.finiteInstantiate, ihf, ihl]

private theorem old_probe_new (rank : Nat) (env : CommonFinite.Environment Row)
    (obs : CommonFinite.Observation Row) (scalar : Scalar) :
    CommonFinite.ProbeAt Common.rowLe rank env
        (CommonCanonicalOpen.finiteInstantiate Fin.elim0 scalar) obs ↔
      CommonNominalFinite.ProbeAt Common.rowLe rank ⟨fun _ => .bottom, env.roles⟩
        (finiteScalar scalar) (newObservation obs) := by
  induction scalar with
  | atom atom => cases atom with
      | var index => exact Fin.elim0 index
      | base scalar =>
          cases rank <;> cases obs <;>
            simp [finiteScalar, newObservation, CommonCanonicalOpen.finiteInstantiate,
              CommonCanonicalOpen.finiteAtom, CommonNominalFinite.ProbeAt,
              CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep,
              CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  | bottom | top =>
      cases rank <;> cases obs <;>
        simp [finiteScalar, newObservation, CommonCanonicalOpen.finiteInstantiate,
          CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
          CommonNominalFinite.MaskedProbeStep, CommonFinite.ProbeAt,
          CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]
  | union first last ihf ihl | inter first last ihf ihl =>
      simp [finiteScalar, CommonCanonicalOpen.finiteInstantiate, ihf, ihl]

theorem scalar_subtype_exact (first last : Scalar) :
    Subtype (scalarMeaning first) (scalarMeaning last) ↔
      Common.Subtype (CommonGroundScalarCasts.meaning first)
        (CommonGroundScalarCasts.meaning last) := by
  have oldObserve (scalar : Scalar) (depth : Nat) :
      Common.observeTy depth (CommonGroundScalarCasts.meaning scalar) =
        CommonCanonicalOpen.finiteInstantiate Fin.elim0 scalar := by
    have unique : (fun index : Fin 0 => Common.observeTy depth (Fin.elim0 index)) =
        Fin.elim0 := funext (fun index => Fin.elim0 index)
    simpa only [CommonGroundScalarCasts.meaning, unique] using
      CommonCanonicalOpen.observe_instantiate depth Fin.elim0 scalar
  constructor
  · intro below depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    rw [oldObserve] at accepted ⊢
    apply (old_probe_new rank env obs first).mpr
    exact (CommonNominalFinite.producerLe_iff_probe _ _).mp (by
      simpa only [observe_scalar] using below 0) rank _ _
      ((old_probe_new rank env obs last).mp accepted)
  · intro below depth
    rw [observe_scalar, observe_scalar]
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    apply (new_probe_old rank env obs first).mpr
    have old := below 0
    rw [oldObserve, oldObserve] at old
    exact (CommonFinite.producerLe_iff_probe _ _).mp old rank _ _
      ((new_probe_old rank env obs last).mp accepted)

end Yulang.CommonNominalGroundAdapter

namespace Yulang.CommonNominalGroundAdapter

open CommonNominalCarrier
open CommonGroundScalarCasts (Scalar)

private theorem scalar_impossible_all (scalar : Scalar)
    (rank : Nat) (env : CommonNominalFinite.Environment Row)
    (obs : CommonNominalFinite.Observation Row)
    (accepted : CommonNominalFinite.ProbeAt Common.rowLe 0
      ⟨fun _ => .bottom, fun _ => []⟩ (finiteScalar scalar) .impossible) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env (finiteScalar scalar) obs := by
  induction scalar with
  | atom atom => cases atom with
      | var index => exact Fin.elim0 index
      | base scalar => contradiction
  | bottom => exact CommonNominalFinite.probeAt_bottom rank obs
  | top => contradiction
  | union first last ihf ihl =>
      apply (CommonNominalFinite.probeAt_union rank _ _ obs).mpr
      exact ⟨ihf accepted.1, ihl accepted.2⟩
  | inter first last ihf ihl =>
      apply (CommonNominalFinite.probeAt_inter rank _ _ obs).mpr
      rcases accepted with before | after
      · exact Or.inl (ihf before)
      · exact Or.inr (ihl after)

private theorem bottom_le (type : Ty) : Subtype .bottom type := by
  intro depth
  apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs _
  exact CommonNominalFinite.probeAt_bottom rank obs

private theorem scalar_nominal_exact (scalar : Scalar) (name : Nat) (arguments : List Argument) :
    Subtype (scalarMeaning scalar) (nominal name arguments) ↔
      Subtype (scalarMeaning scalar) .bottom := by
  constructor
  · intro below depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs _
    rw [observe_scalar]
    apply scalar_impossible_all scalar rank env obs
    have accepted := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0) 0
      (⟨fun _ => .bottom, fun _ => []⟩ : CommonNominalFinite.Environment Row)
      (.nominalHead name arguments.length) (by simp [observe_nominal,
        CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
        CommonNominalFinite.MaskedProbeStep])
    rw [observe_scalar] at accepted
    exact (new_probe_old 0 _ .impossible scalar).mpr
      ((new_probe_old 0 _ (.nominalHead name arguments.length) scalar).mp accepted)
  · intro below
    exact subtype_trans below (bottom_le _)

private theorem scalar_projection (rank : Nat) (env : CommonNominalFinite.Environment Row)
    (obs : CommonNominalFinite.Observation Row) (scalar : Scalar)
    (same : oldObservation obs = .impossible) :
    CommonNominalFinite.ProbeAt Common.rowLe rank env (finiteScalar scalar) obs ↔
      CommonNominalFinite.ProbeAt Common.rowLe rank env (finiteScalar scalar) .impossible := by
  rw [new_probe_old, new_probe_old, same]
  rfl

private theorem nominal_scalar_exact (name : Nat) (arguments : List Argument) (scalar : Scalar) :
    Subtype (nominal name arguments) (scalarMeaning scalar) ↔
      Subtype .top (scalarMeaning scalar) := by
  constructor
  · intro below depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    rw [observe_scalar] at accepted
    have impossible : ¬ CommonNominalFinite.ProbeAt Common.rowLe rank env
        (finiteScalar scalar) .impossible := by
      intro accepted
      have contrad := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0) rank env
        .impossible (by simpa only [observe_scalar] using accepted)
      cases rank <;> simp [observe_nominal, CommonNominalFinite.ProbeAt,
        CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep] at contrad
    cases obs with
    | trivial => cases rank <;> trivial
    | base scalar' =>
        have contrad := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0) rank env
          (.base scalar') (by simpa only [observe_scalar] using accepted)
        cases rank <;> simp [observe_nominal, CommonNominalFinite.ProbeAt,
          CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep] at contrad
    | role name' =>
        have contrad := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0) rank env
          (.role name') (by simpa only [observe_scalar] using accepted)
        cases rank <;> simp [observe_nominal, CommonNominalFinite.ProbeAt,
          CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep] at contrad
    | _ => exact False.elim (impossible ((scalar_projection rank env _ scalar rfl).mp accepted))
  · intro below depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have acceptedTop := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below depth) rank env obs accepted
    have same : obs = .trivial := by
      cases rank <;> cases obs <;>
        simp_all [observeTy, CommonNominalSyntax.Layer.evalAt, CommonNominalFinite.ProbeAt,
          CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]
    subst obs
    exact CommonNominalFinite.probeAt_trivial rank _

end Yulang.CommonNominalGroundAdapter

namespace Yulang.CommonNominalGroundAdapter

open CommonNominalCarrier
open CommonGroundScalarCasts (Scalar)
open CommonGroundNominalCasts (Ground argumentCode)

private def argumentMeaning (scalar : Scalar) : Argument := .inl (scalarMeaning scalar)

def meaning : Ground → Ty
  | .scalar scalar => scalarMeaning scalar
  | .nominal name arguments => nominal name (arguments.map argumentMeaning)

private theorem argument_meaning_equivalent (first last : Scalar) :
    ArgumentEquivalent (argumentMeaning first) (argumentMeaning last) ↔
      argumentCode first = argumentCode last := by
  change (Subtype (scalarMeaning first) (scalarMeaning last) ∧
    Subtype (scalarMeaning last) (scalarMeaning first)) ↔ _
  rw [scalar_subtype_exact, scalar_subtype_exact]
  exact CommonGroundScalarCasts.scalar_normalized_quote_exact first last

private theorem cons_equivalent (a b : Argument) (first last : List Argument) :
    ArgumentsEquivalent (a :: first) (b :: last) ↔
      ArgumentEquivalent a b ∧ ArgumentsEquivalent first last := by
  constructor
  · intro same
    exact ⟨same 0 a b rfl rfl,
      fun index a b left right => same (index + 1) a b left right⟩
  · rintro ⟨head, tail⟩ index a' b' left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst a'
        subst b'
        exact head
    | succ index => exact tail index a' b' left right

private theorem arguments_code_exact (first last : List Scalar) :
    (first.length = last.length ∧
      ArgumentsEquivalent (first.map argumentMeaning) (last.map argumentMeaning)) ↔
      first.map argumentCode = last.map argumentCode := by
  induction first generalizing last with
  | nil =>
      cases last with
      | nil => simp [ArgumentsEquivalent]
      | cons head tail => simp
  | cons head tail ih =>
      cases last with
      | nil => simp
      | cons head' tail' =>
          simp only [List.map_cons, List.length_cons, Nat.add_right_cancel_iff,
            cons_equivalent, argument_meaning_equivalent, List.cons.injEq]
          rw [← ih]
          constructor
          · rintro ⟨size, head, tail⟩; exact ⟨head, size, tail⟩
          · rintro ⟨head, size, tail⟩; exact ⟨size, head, tail⟩

private theorem nominal_meaning_exact (name other : Nat) (first last : List Scalar) :
    Subtype (meaning (.nominal name first)) (meaning (.nominal other last)) ↔
      name = other ∧ first.map argumentCode = last.map argumentCode := by
  rw [meaning, meaning, nominal_regular_invariant_exact]
  simp only [List.length_map, arguments_code_exact]

/-- All source and target descriptions in the explicitly declared finite
scalar/one-nominal ground grammar, with the existing computed normalization
image. Compatibility is the actual existing executable checker. Its semantic
target is the new nested/regular nominal carrier, not a structural encoding. -/
theorem common_ground_cast_compatibility_exact (source target : Ground) :
    CommonGroundNominalCasts.fitsCommonGround.Rel
      (CommonGroundNominalCasts.lower source) (CommonGroundNominalCasts.lower target) ↔
      Subtype (meaning source) (meaning target) := by
  cases source with
  | scalar first =>
      cases target with
      | scalar last =>
          simpa only [CommonGroundNominalCasts.fitsCommonGround, CommonGroundNominalCasts.Rel,
            CommonGroundNominalCasts.lower, CommonGroundScalarCasts.read_quote, meaning] using
            (scalar_subtype_exact first last).symm
      | nominal name arguments =>
          rw [meaning, meaning, scalar_nominal_exact]
          change _ ↔ Subtype (scalarMeaning first) (scalarMeaning .bottom)
          rw [scalar_subtype_exact]
          simp only [CommonGroundNominalCasts.fitsCommonGround, CommonGroundNominalCasts.Rel,
            CommonGroundNominalCasts.lower, CommonGroundScalarCasts.read_quote,
            CommonGroundScalarCasts.read, CommonGroundScalarCasts.meaning,
            CommonCanonicalOpen.instantiate]
  | nominal name arguments =>
      cases target with
      | scalar last =>
          rw [meaning, meaning, nominal_scalar_exact]
          change _ ↔ Subtype (scalarMeaning .top) (scalarMeaning last)
          rw [scalar_subtype_exact]
          simp only [CommonGroundNominalCasts.fitsCommonGround, CommonGroundNominalCasts.Rel,
            CommonGroundNominalCasts.lower, CommonGroundScalarCasts.read_quote,
            CommonGroundScalarCasts.read, CommonGroundScalarCasts.meaning,
            CommonCanonicalOpen.instantiate]
      | nominal other otherArguments =>
          rw [nominal_meaning_exact]
          simp only [CommonGroundNominalCasts.fitsCommonGround, CommonGroundNominalCasts.Rel,
            CommonGroundNominalCasts.lower, CommonGroundScalarCasts.read, Casts.Ty.nominal.injEq]

theorem ground_check_exact (source target : Ground) :
    CommonGroundNominalCasts.fitsCommonGround.check
      (CommonGroundNominalCasts.lower source) (CommonGroundNominalCasts.lower target) = true ↔
      Subtype (meaning source) (meaning target) :=
  (CommonGroundNominalCasts.fitsCommonGround.exact _ _).trans
    (common_ground_cast_compatibility_exact source target)

/-- The previous root-only ground theorem and its actual checker retain
exactly the same meaning on every input of their declared grammar. -/
theorem ground_adapter_preserved (source target : Ground) :
    CommonNominalRoots.Subtype (CommonGroundNominalCasts.meaning source)
      (CommonGroundNominalCasts.meaning target) ↔ Subtype (meaning source) (meaning target) :=
  (CommonGroundNominalCasts.normalized_ground_compatibility_exact source target).symm.trans
    (common_ground_cast_compatibility_exact source target)

end Yulang.CommonNominalGroundAdapter
