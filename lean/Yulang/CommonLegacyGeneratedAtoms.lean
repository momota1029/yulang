import Yulang.CommonLegacyEmptyReflection
import Yulang.PresenceGeneratedChildGrammar

/-!
# Exact legacy erasure of generated atoms on embedded legacy assignments

The translation is syntactic: required fields become old record-width
requirements, exact empty becomes old width, and a whole default has no old
translation. Original slot IDs and every row expression are retained.

Generated upper terms contain no exact-empty/default constructor, and every
proper child of a generated lower term is upper. Consequently translating an
atom is exact whenever its shared assignment already consists of embedded
legacy values. This is not a map from arbitrary common witnesses to legacy
values. Recovering such a simultaneous assignment is the separate remaining
legacy-reflection obligation.
-/

namespace Yulang.CommonLegacyGeneratedAtoms

open CommonLegacyEmptyReflection (legacyModel contextualModel)
open CommonLegacyTyping (assignment)
open PresenceGeneratedChildGrammar (upper lower)

abbrev PresenceTy := Core.PresenceGeneration.TyTerm
abbrev PresenceRow := Core.PresenceGeneration.RowTerm

def eraseRow : PresenceRow α → Inference.RowTerm α
  | .var index => .var index
  | .empty => .empty
  | .join first last => .join (eraseRow first) (eraseRow last)

def eraseType : PresenceTy α → Option (Inference.TyTerm α)
  | .var index => some (.var index)
  | .base scalar => some (.base scalar)
  | .bottom => some .bottom
  | .top => some .top
  | .emptyRecord | .exactEmpty => some .emptyRecord
  | .union first last => do return .union (← eraseType first) (← eraseType last)
  | .inter first last => do return .inter (← eraseType first) (← eraseType last)
  | .pair first last => do return .pair (← eraseType first) (← eraseType last)
  | .record label head tail => do return .record label (← eraseType head) (← eraseType tail)
  | .required label payload => do return .record label (← eraseType payload) .emptyRecord
  | .variant label payload => do return .variant label (← eraseType payload)
  | .arrow input incoming output outgoing =>
      do return .arrow (← eraseType input) (eraseRow incoming) (← eraseType output) (eraseRow outgoing)
  | .recordDefault _ _ _ => none

def OldSyntax : PresenceTy α → Bool
  | .exactEmpty | .recordDefault _ _ _ => false
  | .union first last | .inter first last | .pair first last
  | .record _ first last | .arrow first _ last _ => OldSyntax first && OldSyntax last
  | .required _ payload | .variant _ payload => OldSyntax payload
  | _ => true

theorem eraseRow_eval (values : α → Inference.Comp Common.model.toModel) (row : PresenceRow α) :
    (eraseRow row).eval Common.model.toModel values = row.eval Common.model values := by
  induction row <;> simp_all [eraseRow, Inference.RowTerm.eval, Core.PresenceGeneration.RowTerm.eval]

/-- On the unchanged constructor sublanguage, erasure commutes literally
with evaluation in the inherited common model, for arbitrary common values. -/
theorem erase_eval_inherited (source : PresenceTy α) (erased : Inference.TyTerm α)
    (oldSyntax : OldSyntax source = true) (translated : eraseType source = some erased)
    (values : α → Inference.Comp Common.model.toModel) :
    erased.eval Common.model.toModel values = source.eval Common.model values := by
  induction source generalizing erased with
  | var | base | bottom | top | emptyRecord =>
      simp only [eraseType, Option.some.injEq] at translated
      subst erased
      rfl
  | exactEmpty | recordDefault => cases oldSyntax
  | union first last ihf ihl | inter first last ihf ihl | pair first last ihf ihl
  | record _ first last ihf ihl | arrow first _ last _ ihf ihl =>
      cases firstFound : eraseType first <;> cases lastFound : eraseType last <;>
        simp [eraseType, firstFound, lastFound] at translated
      all_goals
        subst erased
        simp_all [OldSyntax, Inference.TyTerm.eval, Core.PresenceGeneration.TyTerm.eval,
          eraseRow_eval]
  | required label payload ih =>
      cases found : eraseType payload <;> simp [eraseType, found] at translated
      subst erased
      simp_all [OldSyntax, Inference.TyTerm.eval, Core.PresenceGeneration.TyTerm.eval,
        Common.model, Common.required]
  | variant label payload ih =>
      cases found : eraseType payload <;> simp [eraseType, found] at translated
      subst erased
      simp_all [OldSyntax, Inference.TyTerm.eval, Core.PresenceGeneration.TyTerm.eval]

theorem upper_oldSyntax (source : PresenceTy α) (good : upper source = true) : OldSyntax source = true := by
  induction source with
  | var | base | emptyRecord => rfl
  | pair first last ihf ihl | arrow first _ last _ ihf ihl =>
      have both := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihf both.1, ihl both.2⟩
  | required _ _ ih => exact ih good
  | _ => cases good

theorem lower_oldSyntax_or_exact (source : PresenceTy α) (erased : Inference.TyTerm α)
    (good : lower source = true) (translated : eraseType source = some erased) :
    OldSyntax source = true ∨ source = .exactEmpty := by
  cases source with
  | var | base | bottom | top | emptyRecord => exact Or.inl rfl
  | exactEmpty => exact Or.inr rfl
  | union first last | pair first last | record _ first last | arrow first _ last _ =>
      have both := Bool.and_eq_true_iff.mp good
      exact Or.inl (Bool.and_eq_true_iff.mpr ⟨upper_oldSyntax first both.1, upper_oldSyntax last both.2⟩)
  | required _ payload | variant _ payload => exact Or.inl (upper_oldSyntax payload good)
  | inter => cases good
  | recordDefault => cases translated

theorem erased_eval_equivalent (source : PresenceTy α) (erased : Inference.TyTerm α)
    (oldSyntax : OldSyntax source = true) (translated : eraseType source = some erased)
    (values : α → Inference.Comp legacyModel) :
    Common.Equivalent (Common.embedOld (erased.eval legacyModel values))
      (source.eval Common.model (assignment values)) := by
  rw [← erase_eval_inherited source erased oldSyntax translated (assignment values)]
  exact CommonLegacyTyping.eval_value_equivalent values erased

/-- Generated lower heads can be compared with every old regular target.
Only an exact-empty head needs the distinct upper-bound reflection theorem. -/
theorem lower_old_target_exact (source : PresenceTy α) (erased : Inference.TyTerm α)
    (good : lower source = true) (translated : eraseType source = some erased)
    (values : α → Inference.Comp legacyModel) (target : RegularInferenceModel.Ty Common.Row) :
    Common.Subtype (source.eval Common.model (assignment values)) (Common.embedOld target) ↔
      contextualModel.subTy (erased.eval legacyModel values) target := by
  rcases lower_oldSyntax_or_exact source erased good translated with oldSyntax | rfl
  · have same := erased_eval_equivalent source erased oldSyntax translated values
    constructor
    · intro below
      exact (Common.contextual_embedding_exact _ target).mp (Common.subtype_trans same.1 below)
    · intro below
      exact Common.subtype_trans same.2 ((Common.contextual_embedding_exact _ target).mpr below)
  · have equal : erased = .emptyRecord := Option.some.inj translated.symm
    subst erased
    exact CommonLegacyEmptyReflection.exact_empty_upper_contextual_iff target

/-- Both endpoints retain their original IDs. All old value/row assignments
and every generated lower/upper shape are quantified. -/
theorem type_atom_exact (source target : PresenceTy α) (erasedSource erasedTarget : Inference.TyTerm α)
    (sourceGood : lower source = true) (targetGood : upper target = true)
    (sourceTranslated : eraseType source = some erasedSource)
    (targetTranslated : eraseType target = some erasedTarget)
    (values : α → Inference.Comp legacyModel) :
    Common.Subtype (source.eval Common.model (assignment values)) (target.eval Common.model (assignment values)) ↔
      contextualModel.subTy (erasedSource.eval legacyModel values) (erasedTarget.eval legacyModel values) := by
  have targetSame := erased_eval_equivalent target erasedTarget (upper_oldSyntax target targetGood)
    targetTranslated values
  constructor
  · intro below
    exact (lower_old_target_exact source erasedSource sourceGood sourceTranslated values _).mp
      (Common.subtype_trans below targetSame.2)
  · intro below
    exact Common.subtype_trans
      ((lower_old_target_exact source erasedSource sourceGood sourceTranslated values _).mpr below) targetSame.1

def eraseAtom : PresenceNormalForm.Atom α → Option (ConstraintNormalForm.Atom α)
  | .tyLe source target => do return .tyLe (← eraseType source) (← eraseType target)
  | .rowLe source target => some (.rowLe (eraseRow source) (eraseRow target))

def eraseAtoms : List (PresenceNormalForm.Atom α) → Option (List (ConstraintNormalForm.Atom α))
  | [] => some []
  | atom :: atoms => do return (← eraseAtom atom) :: (← eraseAtoms atoms)

theorem contextual_eval_row (values : α → Inference.Comp legacyModel) (row : Inference.RowTerm α) :
    row.eval legacyModel values = row.eval contextualModel values := by
  exact (ProducerContextualRegular.modelMap Common.rowEmpty Common.rowJoin Common.rowLe
    Common.rowLe_trans).eval_row values row

theorem contextual_eval_type (values : α → Inference.Comp legacyModel) (type : Inference.TyTerm α) :
    type.eval legacyModel values = type.eval contextualModel values := by
  exact (ProducerContextualRegular.modelMap Common.rowEmpty Common.rowJoin Common.rowLe
    Common.rowLe_trans).eval_value values type

theorem eraseRow_embedded (values : α → Inference.Comp legacyModel) (row : PresenceRow α) :
    (eraseRow row).eval contextualModel values = row.eval Common.model (assignment values) := by
  rw [← contextual_eval_row]
  exact (CommonLegacyTyping.eval_row values (eraseRow row)).trans (eraseRow_eval (assignment values) row)

/-- A row or value atom is exact under one shared old computation assignment.
Neither arrow variance nor regular old parameter values are restricted. -/
theorem atom_exact (atom : PresenceNormalForm.Atom α) (erased : ConstraintNormalForm.Atom α)
    (good : PresenceGeneratedChildGrammar.GoodAtom atom)
    (translated : eraseAtom atom = some erased) (values : α → Inference.Comp legacyModel) :
    atom.Holds Common.model (assignment values) ↔ erased.Holds contextualModel values := by
  cases atom with
  | tyLe source target =>
      cases sourceFound : eraseType source <;> cases targetFound : eraseType target <;>
        simp [eraseAtom, sourceFound, targetFound] at translated
      subst erased
      change Common.Subtype _ _ ↔ contextualModel.subTy _ _
      simpa only [contextual_eval_type]
        using type_atom_exact source target _ _ good.1 good.2 sourceFound targetFound values
  | rowLe source target =>
      simp only [eraseAtom, Option.some.injEq] at translated
      subst erased
      change Common.rowLe _ _ ↔ Common.rowLe _ _
      rw [eraseRow_embedded, eraseRow_embedded]

/-- The conjunction uses the same original slot assignment in every atom,
including slots shared between positive and negative arrow positions. -/
theorem atoms_exact (atoms : List (PresenceNormalForm.Atom α))
    (erased : List (ConstraintNormalForm.Atom α))
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (translated : eraseAtoms atoms = some erased) (values : α → Inference.Comp legacyModel) :
    PresenceNormalForm.All Common.model (assignment values) atoms ↔
      ConstraintNormalForm.All contextualModel values erased := by
  induction atoms generalizing erased with
  | nil =>
      simp only [eraseAtoms, Option.some.injEq] at translated
      subst erased
      exact iff_of_true (PresenceNormalForm.all_nil _ _) (ConstraintNormalForm.all_nil _ _)
  | cons atom atoms ih =>
      cases atomFound : eraseAtom atom <;> cases atomsFound : eraseAtoms atoms <;>
        simp [eraseAtoms, atomFound, atomsFound] at translated
      subst erased
      have head := atom_exact atom _ (good atom (List.mem_cons_self ..)) atomFound values
      have tail := ih _ (fun item member => good item (List.mem_cons_of_mem _ member)) atomsFound
      simpa only [PresenceNormalForm.All, ConstraintNormalForm.All, List.mem_cons,
        forall_eq_or_imp] using and_congr head tail

/-- Every actual generated packed source clause supplies its endpoint
grammar internally. Successful erasure is the only syntax-side hypothesis;
all old computation assignments remain universally quantified. -/
theorem generated_atoms_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (erased : List (ConstraintNormalForm.Atom (Fin (clause.locals + 1))))
    (translated : eraseAtoms clause.pack = some erased)
    (values : Fin (clause.locals + 1) → Inference.Comp legacyModel) :
    PresenceNormalForm.All Common.model (assignment values) clause.pack ↔
      ConstraintNormalForm.All contextualModel values erased :=
  atoms_exact clause.pack erased
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member) translated values

theorem generated_core_atoms_exact (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (erased : List (ConstraintNormalForm.Atom (Fin (clause.locals + 1))))
    (translated : eraseAtoms clause.pack = some erased)
    (values : Fin (clause.locals + 1) → Inference.Comp legacyModel) :
    PresenceNormalForm.All Common.model (assignment values) clause.pack ↔
      ConstraintNormalForm.All contextualModel values erased :=
  atoms_exact clause.pack erased
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member) translated values

end Yulang.CommonLegacyGeneratedAtoms
