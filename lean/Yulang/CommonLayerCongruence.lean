import Yulang.CommonSyntax
import Yulang.CommonFinitePresence
import Yulang.CommonFiniteMaskOrder

/-!
# Payload congruence for a guarded common layer

Every payload assignment is arbitrary finite common syntax. Pointwise
equivalence quantifies all negative ranks and environments, so substitution
is valid also in an arrow domain. No monotonicity in negative payloads is
assumed. Record tails and default sources retain the current constructor
depth; the special depth-zero default approximation is handled explicitly.

This is the local congruence needed by a constructor-depth induction for
guarded regular closure. It does not construct that closure or assert that
the existing same-depth solver already accepts symbolic payload references.
-/

namespace Yulang.CommonSyntax.Layer

universe u v
variable {Row : Type u} {Index : Type v}

theorem evalAt_congr (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonFinite.Ty Row)
    (same : ∀ index, CommonFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) :
    CommonFinite.ProducerEq leRow (layer.evalAt depth first) (layer.evalAt depth last) := by
  induction layer with
  | base | bottom | top | emptyRecord | exactEmpty => exact CommonFinite.producerEq_refl _
  | union left right ihl ihr => exact CommonFinite.producerEq_union ihl ihr
  | inter left right ihl ihr => exact CommonFinite.producerEq_inter ihl ihr
  | pair left right => exact CommonFinite.producerEq_pair (same left) (same right)
  | record label payload tail ih => exact CommonFinite.producerEq_record label (same payload) ih
  | recordDefault label source fallback ih =>
      cases depth with
      | zero => exact CommonFinite.producerEq_record label (CommonFinite.producerEq_refl .bottom) ih
      | succ previous => exact CommonFinite.producerEq_recordDefault label ih (same fallback)
  | variant label payload => exact CommonFinite.producerEq_variant label (same payload)
  | arrow input incoming output outgoing =>
      exact CommonFinite.producerEq_arrow rowRefl rowTrans incoming outgoing (same input) (same output)
  | mask hidden source ih => exact CommonFinite.producerEq_mask hidden ih

theorem evalAt_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonFinite.Ty Row)
    (same : ∀ index, CommonFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonFinite.Environment Row)
    (observation : CommonFinite.Observation Row) :
    CommonFinite.ProbeAt leRow rank environment (layer.evalAt depth first) observation ↔
      CommonFinite.ProbeAt leRow rank environment (layer.evalAt depth last) observation :=
  (CommonFinite.producerEq_iff_probe _ _).mp
    (evalAt_congr leRow rowRefl rowTrans depth first last same layer) rank environment observation

theorem evalAt_masked_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonFinite.Ty Row)
    (same : ∀ index, CommonFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonFinite.Environment Row)
    (hidden : List Nat) (observation : CommonFinite.Observation Row) :
    CommonFinite.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth first) observation ↔
      CommonFinite.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth last) observation := by
  simpa only [CommonFinite.probeAt_mask] using
    (CommonFinite.producerEq_iff_probe _ _).mp
      (CommonFinite.producerEq_mask hidden (evalAt_congr leRow rowRefl rowTrans depth first last same layer))
      rank environment observation

end Yulang.CommonSyntax.Layer

namespace Yulang.CommonSyntax

universe u
variable {Row : Type u}

/-- Quoting the actual root layer of a state adds no observation delay.
This lets symbolic payload substitution use `.node` while block references
continue to point directly to their shared states. -/
theorem quote_graph_observe_exact (depth : Nat) (state : State Row) :
    observe (graph Row) depth (.node (graph Row state)) = observe (graph Row) depth state := by
  cases depth <;> rfl

end Yulang.CommonSyntax
