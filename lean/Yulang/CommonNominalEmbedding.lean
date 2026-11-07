import Yulang.CommonNominalModel

/-!
# Structural embedding of every old Common graph

The embedding retains old blocks as graph states rather than copying, truncating
or flattening them. Every constructor depth commutes with finite translation.
This is the syntax/observation part of conservativity. Order preservation in
arbitrary extended negative environments is an explicit remaining obligation;
it is not inferred from this observation equality.
-/

namespace Yulang.CommonNominalEmbedding

open CommonNominalCarrier

universe u v

def finite {Row : Type u} : CommonFinite.Ty Row → CommonNominalFinite.Ty Row
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (finite first) (finite last)
  | .inter first last => .inter (finite first) (finite last)
  | .pair first last => .pair (finite first) (finite last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload rest => .record label (finite payload) (finite rest)
  | .recordDefault label source fallback => .recordDefault label (finite source) (finite fallback)
  | .variant label payload => .variant label (finite payload)
  | .arrow arg argRow result resultRow => .arrow (finite arg) argRow (finite result) resultRow
  | .mask hidden source => .mask hidden (finite source)

def embed (type : Common.Ty) : Ty :=
  (CommonNominalSyntax.ofCommonLayer type).map CommonNominalSyntax.State.common

theorem eval_common {Row : Type u} {Index : Type v} (depth : Nat)
    (assignment : Index → CommonFinite.Ty Row) (layer : CommonSyntax.Layer Row Index) :
    (CommonNominalSyntax.ofCommonLayer layer).evalAt depth (finite ∘ assignment) =
      finite (layer.evalAt depth assignment) := by
  induction layer <;> simp [CommonNominalSyntax.ofCommonLayer,
    CommonNominalSyntax.Layer.evalAt, CommonSyntax.Layer.evalAt, finite, *]
  case recordDefault => cases depth <;>
    simp_all [finite]

/-- Arbitrary old finite/regular graph states and every observation depth.
The entire old finite approximation is retained, including exact/default/mask,
arrows and arbitrary rows. No source support or successful solver is assumed. -/
theorem observe_common {Row : Type u} (depth : Nat) (state : CommonSyntax.State Row) :
    CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth
      (.common state) = finite (CommonSyntax.observe (CommonSyntax.graph Row) depth state) := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [CommonNominalSyntax.observe, CommonNominalSyntax.graph,
        CommonNominalSyntax.Layer.evalAt_map, CommonSyntax.observe]
      calc
        _ = (CommonNominalSyntax.ofCommonLayer (CommonSyntax.graph Row state)).evalAt depth
            (finite ∘ CommonSyntax.observe (CommonSyntax.graph Row) depth) := by
          congr 1
          funext child
          exact ih child
        _ = _ := eval_common depth _ _

theorem observe_embed (depth : Nat) (type : Common.Ty) :
    observeTy depth (embed type) = finite (Common.observeTy depth type) := by
  simp only [observeTy, embed, CommonNominalSyntax.Layer.evalAt_map, Common.observeTy]
  calc
    _ = (CommonNominalSyntax.ofCommonLayer type).evalAt depth
        (finite ∘ CommonSyntax.observe (CommonSyntax.graph Common.Row) depth) := by
      congr 1
      funext child
      exact observe_common depth child
    _ = _ := eval_common depth _ _

theorem common_node_observe {Row : Type u} (depth : Nat) (type : CommonSyntax.Ty Row) :
    CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth
      (.common (.node type)) =
    CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth
      (.node ((CommonNominalSyntax.ofCommonLayer type).map CommonNominalSyntax.State.common)) := by
  cases depth <;> rfl

/-- The exact finite comparison still needed for all-old conservativity.
This is a named proposition, not a theorem or a parameter condition on a solved
family. Extended negative environments contain arbitrary new nominal types. -/
def FiniteOrderConservative : Prop :=
  ∀ (first last : CommonFinite.Ty Common.Row),
    CommonNominalFinite.ProducerLe Common.rowLe (finite first) (finite last) ↔
      CommonFinite.ProducerLe Common.rowLe first last

/-- Isolate the remaining semantic lemma from graph bookkeeping. -/
theorem old_order_of_finite_conservativity (conservative : FiniteOrderConservative)
    (first last : Common.Ty) :
    CommonNominalCarrier.Subtype (embed first) (embed last) ↔ Common.Subtype first last := by
  unfold CommonNominalCarrier.Subtype Common.Subtype
  simp only [observe_embed]
  exact forall_congr' fun depth => conservative (Common.observeTy depth first) (Common.observeTy depth last)

end Yulang.CommonNominalEmbedding
