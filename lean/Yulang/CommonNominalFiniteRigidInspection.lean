import Yulang.CommonNominalRigidInspection

/-!
# Guarded finite-observation soundness of nominal rigid inspection

The executable inspector is unchanged. Its ordinary child comparisons are
interpreted at the preceding constructor observation, while row comparisons
keep their full occurrence-set meaning. This supplies the noncircular local
step for cyclic nominal arguments and contravariant arrow inputs.

This module does not assert saturation or soundness of a returned full family.
-/

namespace Yulang.CommonNominalFiniteRigidInspection

open CommonNominalCarrier (Row Ty)
open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)
open CommonNominalRigidInspection (Node inspect typeAtom rowAtom headTerm argumentTerm)

abbrev finiteModel := CommonNominalFinite.model Row Common.rowEmpty Common.rowJoin Common.rowLe

def assignment (rows : Rows → Row) (children : Child → CommonNominalFinite.Ty Row) :
    Child ⊕ Rows → Comp finiteModel
  | .inl child => (children child, Common.rowEmpty)
  | .inr row => (.bottom, rows row)

def Node.evalFinite (rows : Rows → Row) (children : Child → CommonNominalFinite.Ty Row) :
    Node Rows Child → CommonNominalFinite.Ty Row
  | .bottom => .bottom
  | .top => .top
  | .float => .float
  | .base scalar => .base scalar
  | .pair first last => .pair (children first) (children last)
  | .variant label payload => .variant label (children payload)
  | .arrow input incoming output outgoing => .arrow (children input) (rows incoming) (children output) (rows outgoing)
  | .nominal name arguments => .nominal name (arguments.map (Sum.map children rows))

def argumentValue (values : α → Comp finiteModel) : CommonNominalCarrierConstraints.ArgumentTerm α →
    CommonNominalFinite.Ty Row ⊕ Row
  | .value type => .inl (type.eval finiteModel values)
  | .row row => .inr (row.eval finiteModel values)

def Satisfied (values : α → Comp finiteModel) (result : Option (List (Atom α))) : Prop :=
  ∃ atoms, result = some atoms ∧ All finiteModel values atoms

@[simp] theorem satisfied_none (values : α → Comp finiteModel) : ¬ Satisfied values none := by
  simp [Satisfied]

@[simp] theorem satisfied_some (values : α → Comp finiteModel) (atoms : List (Atom α)) :
    Satisfied values (some atoms) ↔ All finiteModel values atoms := by simp [Satisfied]

theorem append_exact (values : α → Comp finiteModel) (first last : Option (List (Atom α))) :
    Satisfied values (CommonNominalCarrierConstraints.append first last) ↔
      Satisfied values first ∧ Satisfied values last := by
  cases first <;> cases last <;>
    simp [CommonNominalCarrierConstraints.append, PresenceNormalForm.all_append]

theorem compile_argument_exact (values : α → Comp finiteModel)
    (first last : CommonNominalCarrierConstraints.ArgumentTerm α) :
    Satisfied values (CommonNominalCarrierConstraints.compileArgument first last) ↔
      CommonNominalFinite.ArgumentEquivalent (leRow := Common.rowLe)
        (argumentValue values first) (argumentValue values last) := by
  cases first <;> cases last <;>
    simp [CommonNominalCarrierConstraints.compileArgument, argumentValue,
      CommonNominalFinite.ArgumentEquivalent, CommonNominalFinite.ProducerEq,
      All, Atom.Holds, finiteModel, CommonNominalFinite.model]

private def Aligned : List (CommonNominalFinite.Ty Row ⊕ Row) →
    List (CommonNominalFinite.Ty Row ⊕ Row) → Prop
  | [], [] => True
  | first :: rest, last :: tail =>
      CommonNominalFinite.ArgumentEquivalent (leRow := Common.rowLe) first last ∧ Aligned rest tail
  | _, _ => False

private theorem aligned_exact (first last : List (CommonNominalFinite.Ty Row ⊕ Row)) :
    Aligned first last ↔ first.length = last.length ∧
      CommonNominalFinite.ArgumentsEquivalent (leRow := Common.rowLe) first last := by
  induction first generalizing last with
  | nil => cases last <;> simp [Aligned, CommonNominalFinite.ArgumentsEquivalent]
  | cons head tail ih =>
      cases last with
      | nil => simp [Aligned]
      | cons head' tail' =>
          simp only [Aligned, ih, List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨same, size, rest⟩
            refine ⟨size, ?_⟩
            intro index a b left right
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
                subst a; subst b
                exact same
            | succ index => exact rest index a b left right
          · rintro ⟨size, same⟩
            exact ⟨same 0 head head' rfl rfl, size,
              fun index a b left right => same (index + 1) a b left right⟩

theorem compile_arguments_exact (values : α → Comp finiteModel)
    (first last : List (CommonNominalCarrierConstraints.ArgumentTerm α)) :
    Satisfied values (CommonNominalCarrierConstraints.compileArguments first last) ↔
      first.length = last.length ∧
        CommonNominalFinite.ArgumentsEquivalent (leRow := Common.rowLe)
          (first.map (argumentValue values)) (last.map (argumentValue values)) := by
  have recursive : Satisfied values (CommonNominalCarrierConstraints.compileArguments first last) ↔
      Aligned (first.map (argumentValue values)) (last.map (argumentValue values)) := by
    induction first generalizing last with
    | nil => cases last <;> simp [CommonNominalCarrierConstraints.compileArguments, Aligned]
    | cons head tail ih =>
        cases last with
        | nil => simp [CommonNominalCarrierConstraints.compileArguments, Aligned]
        | cons head' tail' =>
            simp only [CommonNominalCarrierConstraints.compileArguments, append_exact,
              compile_argument_exact, ih, List.map_cons, Aligned]
  simpa only [List.length_map] using recursive.trans (aligned_exact _ _)

theorem compile_nominal_exact (values : α → Comp finiteModel)
    (first last : CommonNominalCarrierConstraints.HeadTerm α) :
    Satisfied values (CommonNominalCarrierConstraints.compile first last) ↔
      CommonNominalFinite.ProducerLe Common.rowLe
        (.nominal first.name (first.arguments.map (argumentValue values)))
        (.nominal last.name (last.arguments.map (argumentValue values))) := by
  rw [CommonNominalFinite.nominal_finite_invariant_exact Common.rowLe_refl Common.rowLe_trans]
  by_cases same : first.name = last.name
  · simp only [CommonNominalCarrierConstraints.compile, same, ↓reduceIte,
      compile_arguments_exact, List.length_map, true_and]
  · simp [CommonNominalCarrierConstraints.compile, same]

@[simp] theorem argument_term_value (rows : Rows → Row) (children : Child → CommonNominalFinite.Ty Row)
    (argument : Child ⊕ Rows) :
    argumentValue (assignment rows children) (argumentTerm argument) = Sum.map children rows argument := by
  cases argument <;> rfl

/-- Child facts here are finite producer comparisons, not regular Subtype.
Failed head branches cannot supply `valid`; no assignment-dependent test is
used by the actual inspector. -/
theorem inspect_finite_sound (rows : Rows → Row) (children : Child → CommonNominalFinite.Ty Row)
    (source target : Node Rows Child) (valid : Satisfied (assignment rows children) (inspect source target)) :
    CommonNominalFinite.ProducerLe Common.rowLe
      (Node.evalFinite rows children source) (Node.evalFinite rows children target) := by
  cases source <;> cases target
  case nominal.nominal first arguments last arguments' =>
    have below := (compile_nominal_exact (assignment rows children)
      (headTerm first arguments) (headTerm last arguments')).mp valid
    simpa only [headTerm, List.map_map, Function.comp_def, argument_term_value, Node.evalFinite] using below
  all_goals simp only [inspect, satisfied_some, PresenceNormalForm.all_nil] at valid
  all_goals try { change CommonNominalFinite.ProducerLe Common.rowLe .bottom _
                  apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
                  intro rank env obs _
                  cases rank <;> cases obs <;>
                    trivial }
  all_goals try { change CommonNominalFinite.ProducerLe Common.rowLe _ .top
                  apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
                  intro rank env obs accepted
                  cases rank <;> cases obs <;>
                    first | trivial | contradiction }
  case float.float => exact CommonNominalFinite.producerLe_refl _
  case base.base first last =>
    by_cases same : first = last
    · subst last; exact CommonNominalFinite.producerLe_refl _
    · simp [same] at valid
  case pair.pair =>
    apply (CommonNominalFinite.producerLe_pair_iff _ _ _ _).mpr
    simpa [All, Atom.Holds, typeAtom, assignment, TyTerm.eval, finiteModel, CommonNominalFinite.model] using valid
  case variant.variant first payload last payload' =>
    by_cases same : first = last
    · subst last
      apply (CommonNominalFinite.producerLe_variant_iff first _ _).mpr
      simpa [All, Atom.Holds, typeAtom, assignment, TyTerm.eval, finiteModel, CommonNominalFinite.model] using valid
    · simp [same] at valid
  case arrow.arrow =>
    apply (CommonNominalFinite.producerLe_arrow_iff Common.rowLe_refl Common.rowLe_trans _ _ _ _ _ _ _ _).mpr
    simpa [All, Atom.Holds, typeAtom, rowAtom, assignment, TyTerm.eval, RowTerm.eval,
      finiteModel, CommonNominalFinite.model] using valid
  all_goals exact False.elim ((satisfied_none _) valid)

def BelowAt (depth : Nat) (source target : Ty) : Prop :=
  CommonNominalFinite.ProducerLe Common.rowLe
    (CommonNominalCarrier.observeTy depth source) (CommonNominalCarrier.observeTy depth target)

def guardedChildren (depth : Nat) (children : Child → Ty) : Child → CommonNominalFinite.Ty Row :=
  fun child => CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node (children child))

def GuardedAt (depth : Nat) (source target : Ty) : Prop :=
  CommonNominalFinite.ProducerLe Common.rowLe
    (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node source))
    (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node target))

@[simp] theorem guarded_zero (source target : Ty) : GuardedAt 0 source target :=
  CommonNominalFinite.producerLe_refl _

@[simp] theorem guarded_succ (depth : Nat) (source target : Ty) :
    GuardedAt (depth + 1) source target ↔ BelowAt depth source target := Iff.rfl

theorem node_observe (depth : Nat) (rows : Rows → Row) (children : Child → Ty) (node : Node Rows Child) :
    CommonNominalCarrier.observeTy depth (node.eval rows children) =
      Node.evalFinite rows (guardedChildren depth children) node := by
  cases node <;> simp only [Node.eval, CommonNominalCarrier.observeTy, CommonNominalCarrier.pair,
    CommonNominalCarrier.variant, CommonNominalCarrier.arrow, CommonNominalCarrier.nominal,
    CommonNominalSyntax.Layer.evalAt, Node.evalFinite, guardedChildren, List.map_map]
  congr 1
  apply List.map_congr_left
  intro argument _
  cases argument <;> rfl

theorem inspect_at_sound (depth : Nat) (rows : Rows → Row) (children : Child → Ty)
    (source target : Node Rows Child)
    (valid : Satisfied (assignment rows (guardedChildren depth children)) (inspect source target)) :
    BelowAt depth (source.eval rows children) (target.eval rows children) := by
  change CommonNominalFinite.ProducerLe _ _ _
  rw [node_observe, node_observe]
  exact inspect_finite_sound rows (guardedChildren depth children) source target valid

end Yulang.CommonNominalFiniteRigidInspection
