import Yulang.CommonEffectScopedBounds
import Yulang.CommonPresenceTailRegular
import Yulang.CommonMaskOrder

/-! Finite regular equation templates with explicit captured/rigid leaves.
Arbitrary Common captures, exact records, masks and defaults are preserved;
they are not erased into the old carrier. Same-depth equations and negative
guarded references share one solution. These equations do not by themselves
discharge a source's residual subtype/row/rigid-universal obligations. -/
namespace Yulang.CommonEffectScopedRegular
open Common (Ty Row Equivalent)
open CommonSyntax (Layer State)
open CommonEffectRequestGeneration (Computation RowExpr localEnv)
open Core.PresenceGeneration (TyTerm)
open PresenceTailElimination (Mask)

variable {slots labels scopes : Nat}

def reference (assignment : α → Computation) : Fin slots ⊕ α → Fin slots ⊕ State Row
  | .inl index => .inl index
  | .inr name => .inr (.node (assignment name).1)

def refValue (assignment : α → Computation) (values : Fin slots → Ty) : Fin slots ⊕ α → Ty :=
  Sum.elim values (fun name => (assignment name).1)

def compileLayer (assignment : α → Computation) : Layer (RowExpr scopes α) (Fin slots ⊕ α) → Layer Row (Fin slots ⊕ State Row)
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (compileLayer assignment first) (compileLayer assignment last)
  | .inter first last => .inter (compileLayer assignment first) (compileLayer assignment last)
  | .pair first last => .pair (reference assignment first) (reference assignment last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => .record label (reference assignment head) (compileLayer assignment tail)
  | .recordDefault label source fallback => .recordDefault label (compileLayer assignment source) (reference assignment fallback)
  | .variant label body => .variant label (reference assignment body)
  | .arrow input incoming output outgoing => .arrow (reference assignment input) (incoming.eval assignment)
      (reference assignment output) (outgoing.eval assignment)
  | .mask hidden body => .mask hidden (compileLayer assignment body)

def layerValue (assignment : α → Computation) (values : Fin slots → Ty) : Layer (RowExpr scopes α) (Fin slots ⊕ α) → Ty
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (layerValue assignment values first) (layerValue assignment values last)
  | .inter first last => .inter (layerValue assignment values first) (layerValue assignment values last)
  | .pair first last => Common.pair (refValue assignment values first) (refValue assignment values last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => Common.record label (refValue assignment values head) (layerValue assignment values tail)
  | .recordDefault label source fallback => Common.recordDefault label (layerValue assignment values source) (refValue assignment values fallback)
  | .variant label body => Common.variant label (refValue assignment values body)
  | .arrow input incoming output outgoing => Common.arrow (refValue assignment values input) (incoming.eval assignment)
      (refValue assignment values output) (outgoing.eval assignment)
  | .mask hidden body => Common.mask hidden (layerValue assignment values body)

theorem reference_value (assignment : α → Computation) (values : Fin slots → Ty) (index : Fin slots ⊕ α) :
    CommonPresenceTailRegular.payload values (reference assignment index) = refValue assignment values index := by
  cases index <;> rfl

theorem compileLayer_exact (assignment : α → Computation) (values : Fin slots → Ty)
    (layer : Layer (RowExpr scopes α) (Fin slots ⊕ α)) :
    CommonPresenceTailLayers.quoteLayer (CommonPresenceTailRegular.payload values) (compileLayer assignment layer) =
      layerValue assignment values layer := by
  induction layer <;>
    simp_all only [compileLayer, layerValue, CommonPresenceTailLayers.quoteLayer, Layer.map,
      reference_value, Common.pair, Common.record, Common.recordDefault, Common.variant, Common.arrow, Common.mask]

theorem quote_external (type : Ty) (values : Fin slots → Ty) :
    Equivalent (CommonPresenceTailLayers.quoteLayer (CommonPresenceTailRegular.payload values) (type.map Sum.inr)) type := by
  simpa only [CommonPresenceTailLayers.quoteLayer_map, Layer.map_id, Function.comp_def,
    CommonPresenceTailRegular.payload, Sum.elim_inr, id] using
    Common.equivalent_symm (CommonPresenceTailRegular.map_quote_equivalent type (id : State Row → State Row))

inductive Body (slots labels scopes : Nat) (α : Type) where
  | constant : TyTerm α → Body slots labels scopes α
  | atom : Layer (RowExpr scopes α) (Fin slots ⊕ α) → Body slots labels scopes α
  | ref : Fin slots → Body slots labels scopes α
  | union : Body slots labels scopes α → Body slots labels scopes α → Body slots labels scopes α
  | inter : Body slots labels scopes α → Body slots labels scopes α → Body slots labels scopes α
  | mask : Mask labels → Body slots labels scopes α → Body slots labels scopes α
  | record : Nat → (Fin slots ⊕ α) → Body slots labels scopes α → Body slots labels scopes α
  | recordDefault : Nat → Body slots labels scopes α → (Fin slots ⊕ α) → Body slots labels scopes α

def Body.compile (assignment : α → Computation) : Body slots labels scopes α →
    CommonPresenceTailLayers.Body slots labels (CommonPresenceTailRegular.Payload slots)
  | .constant term => .atom ((term.eval Common.model assignment).map Sum.inr)
  | .atom layer => .atom (compileLayer assignment layer)
  | .ref index => .ref index
  | .union first last => .union (compile assignment first) (compile assignment last)
  | .inter first last => .inter (compile assignment first) (compile assignment last)
  | .mask hidden body => .mask hidden (compile assignment body)
  | .record label head tail => .record label (reference assignment head) (compile assignment tail)
  | .recordDefault label source fallback => .recordDefault label (compile assignment source) (reference assignment fallback)

def Body.value (assignment : α → Computation) (values : Fin slots → Ty) : Body slots labels scopes α → Ty
  | .constant term => term.eval Common.model assignment
  | .atom layer => layerValue assignment values layer
  | .ref index => values index
  | .union first last => .union (value assignment values first) (value assignment values last)
  | .inter first last => .inter (value assignment values first) (value assignment values last)
  | .mask hidden body => Common.mask hidden.names (value assignment values body)
  | .record label head tail => Common.record label (refValue assignment values head) (value assignment values tail)
  | .recordDefault label source fallback => Common.recordDefault label (value assignment values source) (refValue assignment values fallback)

theorem Body.compile_exact (body : Body slots labels scopes α) (assignment : α → Computation) (values : Fin slots → Ty) :
    Equivalent (((body.compile assignment).quote (CommonPresenceTailRegular.payload values)).eval values)
      (body.value assignment values) := by
  induction body with
  | constant term => exact quote_external (term.eval Common.model assignment) values
  | atom layer => rw [Body.compile, CommonPresenceTailLayers.Body.quote, CommonPresenceTailElimination.Body.eval,
      compileLayer_exact]; exact Common.equivalent_refl _
  | ref index => exact Common.equivalent_refl _
  | union first last ihf ihl => exact ⟨Common.common_union_mono ihf.1 ihl.1, Common.common_union_mono ihf.2 ihl.2⟩
  | inter first last ihf ihl => exact ⟨Common.common_inter_mono ihf.1 ihl.1, Common.common_inter_mono ihf.2 ihl.2⟩
  | mask hidden body ih => exact Common.common_mask_type_congr hidden.names ih
  | record label head tail ih =>
    simpa only [Body.compile, Body.value, CommonPresenceTailLayers.Body.quote, CommonPresenceTailElimination.Body.eval,
      reference_value] using
      (show Equivalent (Common.record label (refValue assignment values head) _) (Common.record label (refValue assignment values head) _) from
        ⟨Common.common_record_mono label (Common.subtype_refl _) ih.1, Common.common_record_mono label (Common.subtype_refl _) ih.2⟩)
  | recordDefault label source fallback ih =>
    simpa only [Body.compile, Body.value, CommonPresenceTailLayers.Body.quote, CommonPresenceTailElimination.Body.eval,
      reference_value] using Common.common_default_congr label ih (Common.equivalent_refl (refValue assignment values fallback))

abbrev Graph (slots labels scopes : Nat) (α : Type) := Fin slots → Body slots labels scopes α

def compile (graph : Graph slots labels scopes α) (assignment : α → Computation) : CommonPresenceTailRegular.Graph slots labels :=
  fun index => (graph index).compile assignment

def Models (graph : Graph slots labels scopes α) (assignment : α → Computation) (values : Fin slots → Ty) : Prop :=
  ∀ index, Equivalent ((graph index).value assignment values) (values index)

theorem compile_models (graph : Graph slots labels scopes α) (assignment : α → Computation) (values : Fin slots → Ty) :
    CommonPresenceTailRegular.Models (compile graph assignment) values ↔ Models graph assignment values := by
  constructor
  · intro model index
    exact Common.equivalent_trans (Common.equivalent_symm ((graph index).compile_exact assignment values)) (model index)
  · intro model index
    exact Common.equivalent_trans ((graph index).compile_exact assignment values) (model index)

def instantiate (graph : Graph slots labels scopes α) (assignment : α → Computation) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  CommonPresenceTailRegular.solveBlock (compile graph assignment) parameters

theorem all_parameters_models (graph : Graph slots labels scopes α) (assignment : α → Computation) (parameters : Fin slots → Ty) :
    Models graph assignment (instantiate graph assignment parameters) :=
  (compile_models graph assignment _).mp (CommonPresenceTailRegular.solveBlock_models _ parameters)

theorem model_retraction (graph : Graph slots labels scopes α) (assignment : α → Computation) (values : Fin slots → Ty)
    (model : Models graph assignment values) :
    ∀ index, Equivalent (instantiate graph assignment values index) (values index) :=
  CommonPresenceTailRegular.solveBlock_retract _ values ((compile_models graph assignment values).mpr model)

/-- Every local assignment has a solution constructed by the SAME finite
graph and the fixed bottom-parameter policy, with all captures unchanged. -/
theorem uniform_canonical_models (graph : Graph slots labels scopes (α ⊕ Fin count)) (assignment : α → Computation) :
    ∀ locals : Fin count → Ty,
      Models graph (localEnv assignment locals) (instantiate graph (localEnv assignment locals) (fun _ => .bottom)) :=
  fun _ => all_parameters_models graph _ _
theorem all_instances_exact (graph : Graph slots labels scopes α) (assignment : α → Computation) (values : Fin slots → Ty) :
    Models graph assignment values ↔
      ∃ parameters : Fin slots → Ty, ∀ index, Equivalent (instantiate graph assignment parameters index) (values index) :=
  (compile_models graph assignment values).symm.trans
    (CommonPresenceTailRegular.guarded_solved_instances_exact (compile graph assignment) values)

/-- Recovery of arbitrary local-dependent INTERNAL equation valuations.
Function-valued parameters here expose that dependency explicitly; existence
already has the ordinary fixed bottom policy in uniform_canonical_models. -/
theorem scoped_all_instances_exact (graph : Graph slots labels scopes (α ⊕ Fin count)) (assignment : α → Computation)
    (values : (Fin count → Ty) → Fin slots → Ty) :
    (∀ locals, Models graph (localEnv assignment locals) (values locals)) ↔
      ∃ parameters : (Fin count → Ty) → Fin slots → Ty,
        ∀ locals index, Equivalent (instantiate graph (localEnv assignment locals) (parameters locals) index) (values locals index) := by
  constructor
  · intro model
    exact ⟨values, fun locals => model_retraction graph _ _ (model locals)⟩
  · rintro ⟨parameters, same⟩ locals
    exact (all_instances_exact graph (localEnv assignment locals) (values locals)).mpr ⟨parameters locals, same locals⟩
end Yulang.CommonEffectScopedRegular
