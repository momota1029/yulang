import Yulang.CommonNominalSyntax
import Yulang.CommonNominalFinitePresence
import Yulang.CommonNominalFiniteMaskOrder

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

namespace Yulang.CommonNominalSyntax.Layer

universe u v
variable {Row : Type u} {Index : Type v}

theorem evalAt_congr (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFinite.Ty Row)
    (same : ∀ index, CommonNominalFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) :
    CommonNominalFinite.ProducerEq leRow (layer.evalAt depth first) (layer.evalAt depth last) := by
  induction layer with
  | base | float | bottom | top | emptyRecord | exactEmpty => exact CommonNominalFinite.producerEq_refl _
  | union left right ihl ihr => exact CommonNominalFinite.producerEq_union ihl ihr
  | inter left right ihl ihr => exact CommonNominalFinite.producerEq_inter ihl ihr
  | pair left right => exact CommonNominalFinite.producerEq_pair (same left) (same right)
  | record label payload tail ih => exact CommonNominalFinite.producerEq_record label (same payload) ih
  | recordDefault label source fallback ih =>
      cases depth with
      | zero => exact CommonNominalFinite.producerEq_record label (CommonNominalFinite.producerEq_refl .bottom) ih
      | succ previous => exact CommonNominalFinite.producerEq_recordDefault label ih (same fallback)
  | variant label payload => exact CommonNominalFinite.producerEq_variant label (same payload)
  | arrow input incoming output outgoing =>
      exact CommonNominalFinite.producerEq_arrow rowRefl rowTrans incoming outgoing (same input) (same output)
  | mask hidden source ih => exact CommonNominalFinite.producerEq_mask hidden ih
  | nominal name arguments =>
      have comparison (first last : Index → CommonNominalFinite.Ty Row)
          (same : ∀ index, CommonNominalFinite.ProducerEq leRow (first index) (last index)) :
          CommonNominalFinite.ProducerLe leRow
            (.nominal name (arguments.map (Sum.map first id)))
            (.nominal name (arguments.map (Sum.map last id))) := by
        apply CommonNominalFinite.nominal_invariant_backward (leRow := leRow) rowTrans rfl
          (by simp only [List.length_map])
        intro index a b left right
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp left
        have within : index < arguments.length := by simpa only [List.length_map] using bound
        have firstAt : (arguments.map (Sum.map first id))[index]? =
            some (Sum.map first id arguments[index]) := by simp [within]
        have lastAt : (arguments.map (Sum.map last id))[index]? =
            some (Sum.map last id arguments[index]) := by simp [within]
        have aEq := Option.some.inj (left.symm.trans firstAt)
        have bEq := Option.some.inj (right.symm.trans lastAt)
        subst a; subst b
        simp only [List.getElem_map]
        cases original : arguments[index] with
        | inl parameter => exact same parameter
        | inr row => exact ⟨rowRefl row, rowRefl row⟩
      exact ⟨comparison first last same, comparison last first (fun index => ⟨(same index).2, (same index).1⟩)⟩

theorem evalAt_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFinite.Ty Row)
    (same : ∀ index, CommonNominalFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonNominalFinite.Environment Row)
    (observation : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.ProbeAt leRow rank environment (layer.evalAt depth first) observation ↔
      CommonNominalFinite.ProbeAt leRow rank environment (layer.evalAt depth last) observation :=
  (CommonNominalFinite.producerEq_iff_probe _ _).mp
    (evalAt_congr leRow rowRefl rowTrans depth first last same layer) rank environment observation

theorem evalAt_masked_probe_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (depth : Nat) (first last : Index → CommonNominalFinite.Ty Row)
    (same : ∀ index, CommonNominalFinite.ProducerEq leRow (first index) (last index))
    (layer : Layer Row Index) (rank : Nat) (environment : CommonNominalFinite.Environment Row)
    (hidden : List Nat) (observation : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth first) observation ↔
      CommonNominalFinite.MaskedProbeAt leRow rank environment hidden (layer.evalAt depth last) observation := by
  simpa only [CommonNominalFinite.probeAt_mask] using
    (CommonNominalFinite.producerEq_iff_probe _ _).mp
      (CommonNominalFinite.producerEq_mask hidden (evalAt_congr leRow rowRefl rowTrans depth first last same layer))
      rank environment observation

end Yulang.CommonNominalSyntax.Layer

namespace Yulang.CommonNominalSyntax

universe u
variable {Row : Type u}

/-- Quoting the actual root layer of a state adds no observation delay.
This lets symbolic payload substitution use `.node` while block references
continue to point directly to their shared states. -/
theorem quote_graph_observe_exact (depth : Nat) (state : State Row) :
    observe (graph Row) depth (.node (graph Row state)) = observe (graph Row) depth state := by
  cases depth <;> rfl

end Yulang.CommonNominalSyntax
