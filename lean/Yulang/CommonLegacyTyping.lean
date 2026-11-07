import Yulang.CommonLegacy
import Yulang.CommonFinitePresence
import Yulang.CorePresenceLegacyPreservation

/-!
# Concrete preservation of legacy typing in the common presence carrier

The old and new constructor references are not literally identical syntax:
an embedded old node is a legacy state, while a newly constructed common node
is an ordinary node. Their finite observations coincide at every depth. This
module proves constructor/evaluation preservation at that actual observation
boundary and maps every existential formula witness with its original row.

The result is preservation into the independent common presence typing
judgment, including old supported inference instances. It does not assert a
new solved `Core.infer` entry, nor reflect arbitrary new existential witnesses
back to legacy syntax.
-/

namespace Yulang.CommonLegacyTyping

open Inference
open Common (Ty Row)

abbrev oldModel := SourcePrincipalInference.model Common.rowAlgebra
abbrev newModel := Common.model.toModel

def assignment (values : α → Comp oldModel) : α → Comp newModel :=
  fun index => Common.embedComp (values index)

@[simp] theorem assignment_extend (values : α → Comp oldModel) (result : Comp oldModel) :
    assignment (extend values result) = extend (assignment values) (Common.embedComp result) := by
  funext index
  cases index <;> rfl

/-- The quotation discrepancy is observational only, at every finite depth. -/
theorem legacy_quote_observe (depth : Nat) (type : oldModel.Ty) :
    CommonSyntax.observe (CommonSyntax.graph Row) depth
        (.legacy (.node type)) =
      CommonSyntax.observe (CommonSyntax.graph Row) depth (.node (Common.embedOld type)) := by
  cases depth <;> rfl

theorem eval_row (values : α → Comp oldModel) (term : RowTerm α) :
    term.eval oldModel values = term.eval newModel (assignment values) := by
  induction term with
  | var => rfl
  | empty => rfl
  | join first last ihf ihl =>
      change Common.rowJoin _ _ = Common.rowJoin _ _
      rw [ihf, ihl]

/-- Every symbolic constructor commutes with embedding at every finite
observation. Variables may contain arbitrary old regular graphs. -/
theorem eval_value_observe (values : α → Comp oldModel) (term : TyTerm α) (depth : Nat) :
    Common.observeTy depth (Common.embedOld (term.eval oldModel values)) =
      Common.observeTy depth (term.eval newModel (assignment values)) := by
  induction term generalizing depth with
  | var | base | bottom | top | emptyRecord => rfl
  | union first last ihf ihl =>
      change CommonFinite.Ty.union
        (Common.observeTy depth (Common.embedOld (first.eval oldModel values)))
        (Common.observeTy depth (Common.embedOld (last.eval oldModel values))) =
        CommonFinite.Ty.union
          (Common.observeTy depth (first.eval newModel (assignment values)))
          (Common.observeTy depth (last.eval newModel (assignment values)))
      exact congr (congrArg CommonFinite.Ty.union (ihf depth)) (ihl depth)
  | inter first last ihf ihl =>
      change CommonFinite.Ty.inter
        (Common.observeTy depth (Common.embedOld (first.eval oldModel values)))
        (Common.observeTy depth (Common.embedOld (last.eval oldModel values))) =
        CommonFinite.Ty.inter
          (Common.observeTy depth (first.eval newModel (assignment values)))
          (Common.observeTy depth (last.eval newModel (assignment values)))
      exact congr (congrArg CommonFinite.Ty.inter (ihf depth)) (ihl depth)
  | pair first last ihf ihl =>
      cases depth with
      | zero => rfl
      | succ depth =>
          change CommonFinite.Ty.pair
            (Common.observeTy depth (Common.embedOld (first.eval oldModel values)))
            (Common.observeTy depth (Common.embedOld (last.eval oldModel values))) =
            CommonFinite.Ty.pair
              (Common.observeTy depth (first.eval newModel (assignment values)))
              (Common.observeTy depth (last.eval newModel (assignment values)))
          rw [ihf, ihl]
  | record label head tail ihh iht =>
      cases depth with
      | zero =>
          change CommonFinite.Ty.record label .bottom
            (Common.observeTy 0 (Common.embedOld (tail.eval oldModel values))) =
            CommonFinite.Ty.record label .bottom
              (Common.observeTy 0 (tail.eval newModel (assignment values)))
          rw [iht]
      | succ depth =>
          change CommonFinite.Ty.record label
            (Common.observeTy depth (Common.embedOld (head.eval oldModel values)))
            (Common.observeTy (depth + 1) (Common.embedOld (tail.eval oldModel values))) =
            CommonFinite.Ty.record label
              (Common.observeTy depth (head.eval newModel (assignment values)))
              (Common.observeTy (depth + 1) (tail.eval newModel (assignment values)))
          rw [ihh, iht]
  | variant label payload ih =>
      cases depth with
      | zero => rfl
      | succ depth =>
          change CommonFinite.Ty.variant label
            (Common.observeTy depth (Common.embedOld (payload.eval oldModel values))) =
            CommonFinite.Ty.variant label
              (Common.observeTy depth (payload.eval newModel (assignment values)))
          rw [ih]
  | arrow input inputRow output outputRow ihi iho =>
      cases depth with
      | zero =>
          change CommonFinite.Ty.arrow .bottom (inputRow.eval oldModel values) .bottom
            (outputRow.eval oldModel values) =
            CommonFinite.Ty.arrow .bottom (inputRow.eval newModel (assignment values)) .bottom
              (outputRow.eval newModel (assignment values))
          rw [eval_row values inputRow, eval_row values outputRow]
          rfl
      | succ depth =>
          change CommonFinite.Ty.arrow
            (Common.observeTy depth (Common.embedOld (input.eval oldModel values)))
            (inputRow.eval oldModel values)
            (Common.observeTy depth (Common.embedOld (output.eval oldModel values)))
            (outputRow.eval oldModel values) =
            CommonFinite.Ty.arrow
              (Common.observeTy depth (input.eval newModel (assignment values)))
              (inputRow.eval newModel (assignment values))
              (Common.observeTy depth (output.eval newModel (assignment values)))
              (outputRow.eval newModel (assignment values))
          rw [ihi, iho, eval_row values inputRow, eval_row values outputRow]

theorem eval_value_equivalent (values : α → Comp oldModel) (term : TyTerm α) :
    Common.Equivalent (Common.embedOld (term.eval oldModel values))
      (term.eval newModel (assignment values)) := by
  constructor <;> intro depth
  · rw [eval_value_observe]
    exact CommonFinite.producerLe_refl _
  · rw [eval_value_observe]
    exact CommonFinite.producerLe_refl _

theorem subtype_preserved {first last : oldModel.Ty} (below : oldModel.subTy first last) :
    Common.Subtype (Common.embedOld first) (Common.embedOld last) :=
  (Common.contextual_embedding_exact first last).mpr
    (ProducerContextualRegular.structural_subtype_preserved
      (graph := RegularInferenceModel.graph Row) (leRow := Common.rowLe) Common.rowLe_trans below)

/-- No witnesses are discarded: both the value and unchanged row of every
existential slot are mapped recursively, including captured free slots. -/
theorem formula_preserved (formula : Formula α) (values : α → Comp oldModel)
    (held : formula.Holds oldModel values) :
    formula.Holds newModel (assignment values) := by
  induction formula with
  | top => trivial
  | bot => exact held
  | and first last ihf ihl => exact ⟨ihf values held.1, ihl values held.2⟩
  | or first last ihf ihl =>
      exact held.elim (fun proof => Or.inl (ihf values proof))
        (fun proof => Or.inr (ihl values proof))
  | tyLe first last =>
      exact Common.subtype_trans (eval_value_equivalent values first).2
        (Common.subtype_trans (subtype_preserved held) (eval_value_equivalent values last).1)
  | rowLe first last =>
      change Common.rowLe (first.eval newModel (assignment values))
        (last.eval newModel (assignment values))
      rw [← eval_row values first, ← eval_row values last]
      exact held
  | existsSlot body ih =>
      obtain ⟨witness, proof⟩ := held
      exact ⟨Common.embedComp witness, by simpa only [assignment_extend] using ih _ proof⟩

/-- Every old closed derivation and result is covered. This theorem has no
source-support or inference-success premise. -/
theorem closed_typing_preserved (expression : Expr) (result : Comp oldModel)
    (typed : Typing oldModel [] expression result) :
    Typing newModel [] expression (Common.embedComp result) := by
  have original := (principal_exact oldModel expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) result).mpr typed
  have moved := formula_preserved (principal ([] : SchemeEnv Empty) expression)
    (extend Empty.elim result) original
  have emptyAssignment : assignment (Empty.elim : Empty → Comp oldModel) = Empty.elim := by
    funext index
    exact Empty.elim index
  rw [assignment_extend, emptyAssignment] at moved
  exact (principal_exact newModel expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) (Common.embedComp result)).mp moved

/-- The presence compatibility laws follow from the concrete carrier. -/
theorem compatible : Core.PresenceGeneration.LegacyPreservation.Compatible Common.model where
  trans := Common.subtype_trans
  exactEmpty_width := fun _ => CommonFinite.exactEmpty_below_width
  required_eq := Common.required_as_width_tail

theorem presence_typing_preserved (expression : Expr) (result : Comp oldModel)
    (typed : Typing oldModel [] expression result) :
    Core.PresenceGeneration.Typing Common.model [] expression (Common.embedComp result) :=
  Core.PresenceGeneration.LegacyPreservation.closed_typing_preserved Common.model compatible
    expression _ (closed_typing_preserved expression result typed)

/-- The actual old inference instance implies independent common presence
typing, with its result row unchanged. This does not define a new instance. -/
theorem legacy_instances_preserved (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true) (result : Comp oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    Core.PresenceGeneration.Typing Common.model [] expression (Common.embedComp result) :=
  presence_typing_preserved expression result
    ((SourcePrincipalInference.infer_instances_exact Common.rowAlgebra Common.rowLe_antisymm
      expression supported result).mp accepted)

theorem legacy_core_instances_preserved (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true) (result : Comp oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    Core.Typing (Core.PresenceGeneration.CoreRules.model Common.model) []
      (Core.Required.embed expression) (Common.embedComp result) :=
  Core.PresenceGeneration.CoreRules.preserved
    (legacy_instances_preserved expression supported result accepted)

end Yulang.CommonLegacyTyping
