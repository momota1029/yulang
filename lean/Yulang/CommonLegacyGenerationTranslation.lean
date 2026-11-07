import Yulang.CommonLegacyGeneratedErasure

/-!
# Literal correspondence of the old and presence generators

This translation preserves the actual finite clause shape, all binder slots,
all captured names and both value-let alternatives. Required fields become
the old record-width constructor and exact empty becomes old width.

`translateType` is total only to simplify structural commutation proofs: its
arbitrary bottom case for a whole default has no semantic assertion. Every
application to a generated legacy-source clause is default-free, and the
successful partial `eraseType`/`eraseAtoms` translation agrees with it.
-/

namespace Yulang.CommonLegacyGenerationTranslation

open Core.PresenceGeneration PresenceNormalForm
open CommonLegacyGeneratedAtoms
open CommonLegacyGeneratedErasure
open Inference (Expr)

def translateType : TyTerm α → Inference.TyTerm α
  | .var index => .var index
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (translateType first) (translateType last)
  | .inter first last => .inter (translateType first) (translateType last)
  | .pair first last => .pair (translateType first) (translateType last)
  | .emptyRecord | .exactEmpty => .emptyRecord
  | .record label head tail => .record label (translateType head) (translateType tail)
  | .required label payload => .record label (translateType payload) .emptyRecord
  | .variant label payload => .variant label (translateType payload)
  | .arrow input incoming output outgoing =>
      .arrow (translateType input) (eraseRow incoming) (translateType output) (eraseRow outgoing)
  | .recordDefault _ _ _ => .bottom

def translateComp (term : CompTerm α) : Inference.CompTerm α :=
  ⟨translateType term.ty, eraseRow term.row⟩

def translateFormula : Formula α → Inference.Formula α
  | .top => .top
  | .bot => .bot
  | .and first last => .and (translateFormula first) (translateFormula last)
  | .or first last => .or (translateFormula first) (translateFormula last)
  | .tyLe source target => .tyLe (translateType source) (translateType target)
  | .rowLe source target => .rowLe (eraseRow source) (eraseRow target)
  | .existsSlot body => .existsSlot (translateFormula body)

def translateEnv (schemes : SchemeEnv α) : Inference.SchemeEnv α := schemes.map translateFormula

@[simp] theorem row_rename (rename : α → β) (term : RowTerm α) :
    eraseRow (term.rename rename) = (eraseRow term).rename rename := by
  induction term <;> simp_all [eraseRow, RowTerm.rename, Inference.RowTerm.rename]

@[simp] theorem type_rename (rename : α → β) (term : TyTerm α) :
    translateType (term.rename rename) = (translateType term).rename rename := by
  induction term <;> simp_all [translateType, TyTerm.rename, Inference.TyTerm.rename]

@[simp] theorem comp_rename (rename : α → β) (term : CompTerm α) :
    translateComp (term.rename rename) = (translateComp term).rename rename := by
  simp [translateComp, CompTerm.rename, Inference.CompTerm.rename]

@[simp] theorem formula_rename (rename : α → β) (formula : Formula α) :
    translateFormula (formula.rename rename) = (translateFormula formula).rename rename := by
  induction formula generalizing β <;>
    simp_all [translateFormula, Formula.rename, Inference.Formula.rename]

@[simp] theorem env_rename (rename : α → β) (schemes : SchemeEnv α) :
    translateEnv (schemes.rename rename) = (translateEnv schemes).rename rename := by
  simp [translateEnv, SchemeEnv.rename, Inference.SchemeEnv.rename, List.map_map, Function.comp_def]

@[simp] theorem env_lift (schemes : SchemeEnv α) :
    translateEnv schemes.lift = (translateEnv schemes).lift := env_rename some schemes

@[simp] theorem env_cons (scheme : Scheme α) (schemes : SchemeEnv α) :
    translateEnv (scheme :: schemes) = translateFormula scheme :: translateEnv schemes := rfl

@[simp] theorem row_subst (subst : α → CompTerm β) (term : RowTerm α) :
    eraseRow (term.subst subst) = (eraseRow term).subst (fun index => translateComp (subst index)) := by
  induction term <;> simp_all [eraseRow, RowTerm.subst, Inference.RowTerm.subst, translateComp]

@[simp] theorem type_subst (subst : α → CompTerm β) (term : TyTerm α) :
    translateType (term.subst subst) = (translateType term).subst (fun index => translateComp (subst index)) := by
  induction term <;>
    simp_all [translateType, TyTerm.subst, Inference.TyTerm.subst, translateComp]

@[simp] theorem comp_subst (subst : α → CompTerm β) (term : CompTerm α) :
    translateComp (term.subst subst) = (translateComp term).subst (fun index => translateComp (subst index)) := by
  simp [translateComp, CompTerm.subst, Inference.CompTerm.subst]

theorem translated_liftSubst (subst : α → CompTerm β) :
    (fun index => translateComp (liftSubst subst index)) =
      Inference.liftSubst (fun index => translateComp (subst index)) := by
  funext index
  cases index with
  | none => rfl
  | some index => exact comp_rename some (subst index)

@[simp] theorem formula_subst (subst : α → CompTerm β) (formula : Formula α) :
    translateFormula (formula.subst subst) =
      (translateFormula formula).subst (fun index => translateComp (subst index)) := by
  induction formula generalizing β with
  | top | bot => rfl
  | and first last ihf ihl | or first last ihf ihl =>
      simp [translateFormula, Formula.subst, Inference.Formula.subst, ihf, ihl]
  | tyLe | rowLe => simp [translateFormula, Formula.subst, Inference.Formula.subst]
  | existsSlot body ih =>
      simp only [Formula.subst, translateFormula, Inference.Formula.subst, ih, translated_liftSubst]

@[simp] theorem translate_var (index : α) :
    translateComp (CompTerm.var index) = Inference.CompTerm.var index := rfl

@[simp] theorem translate_pure (type : TyTerm α) :
    translateComp (CompTerm.pure type) = Inference.CompTerm.pure (translateType type) := rfl

@[simp] theorem translate_arrow (input output : CompTerm α) :
    translateType (CompTerm.arrow input output) =
      Inference.CompTerm.arrow (translateComp input) (translateComp output) := rfl

@[simp] theorem translate_compLe (source target : CompTerm α) :
    translateFormula (Formula.compLe source target) =
      Inference.Formula.compLe (translateComp source) (translateComp target) := rfl

@[simp] theorem translate_mono (term : CompTerm α) :
    translateFormula (Scheme.mono term) = Inference.Scheme.mono (translateComp term) := by
  simp only [Scheme.mono, Inference.Scheme.mono, translate_compLe, comp_rename, translate_var]

@[simp] theorem translate_instantiate (scheme : Scheme α) (output : CompTerm α) :
    translateFormula (scheme.instantiate output) =
      Inference.Scheme.instantiate (translateFormula scheme) (translateComp output) := by
  simp only [Scheme.instantiate, Inference.Scheme.instantiate, formula_subst]
  congr 1
  funext index
  cases index <;> rfl

@[simp] theorem translate_lookup (schemes : SchemeEnv α) (index : Nat) (output : CompTerm α) :
    translateFormula (Scheme.lookup schemes index output) =
      Inference.Scheme.lookup (translateEnv schemes) index (translateComp output) := by
  simp only [Scheme.lookup, Inference.Scheme.lookup, translateEnv, List.getElem?_map]
  cases found : schemes[index]? <;> simp [translateFormula]

theorem clean_translation (term : TyTerm α) (good : clean term = true) :
    eraseType term = some (translateType term) := by
  induction term <;> simp_all [clean, eraseType, translateType]

/-- The two real generators have literally the same translated output.
Every captured input scheme and every symbolic output remain quantified. -/
theorem generate_translation (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (schemes : SchemeEnv α) (output : CompTerm α) :
    translateFormula (generate schemes expression output) =
      Inference.generate (translateEnv schemes) expression (translateComp output) := by
  induction expression generalizing α with
  | var index => exact translate_lookup schemes index output
  | lit | emptyRecord => rfl
  | recordDefault => cases required
  | lam body ih =>
      simp [generate, Inference.generate, translateFormula, ih required, env₂, Inference.env₂,
        translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        CompTerm.arrow, Inference.CompTerm.arrow,
        fresh₀, fresh₁, Inference.fresh₀, Inference.fresh₁, lift₂, Inference.lift₂,
        CompTerm.var, Inference.CompTerm.var, CompTerm.pure, Inference.CompTerm.pure]
  | app function argument ihf iha =>
      have both := Bool.and_eq_true_iff.mp required
      simp [generate, Inference.generate, translateFormula, ihf both.1, iha both.2,
        env₃, Inference.env₃, translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        CompTerm.arrow, Inference.CompTerm.arrow, fresh₀₃, fresh₁₃, fresh₂₃,
        Inference.fresh₀₃, Inference.fresh₁₃, Inference.fresh₂₃, lift₃, Inference.lift₃,
        CompTerm.var, Inference.CompTerm.var]
  | letE definition body ihd ihb =>
      have both := Bool.and_eq_true_iff.mp required
      simp only [generate, Inference.generate]
      split <;>
        simp [translateFormula, ihd both.1, ihb both.2, env₂, Inference.env₂,
          translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
          fresh₀, fresh₁, Inference.fresh₀, Inference.fresh₁,
          lift₂, Inference.lift₂, CompTerm.var, Inference.CompTerm.var,
          CompTerm.pure, Inference.CompTerm.pure]
  | branch condition yes no ihc ihy ihn =>
      have both := Bool.and_eq_true_iff.mp required
      have first := Bool.and_eq_true_iff.mp both.1
      simp [generate, Inference.generate, translateFormula, ihc first.1, ihy first.2, ihn both.2,
        env₃, Inference.env₃, translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        fresh₀₃, fresh₁₃, fresh₂₃, Inference.fresh₀₃, Inference.fresh₁₃, Inference.fresh₂₃,
        lift₃, Inference.lift₃, CompTerm.var, Inference.CompTerm.var]
  | pair first last ihf ihl | record _ first last ihf ihl =>
      have both := Bool.and_eq_true_iff.mp required
      simp [generate, Inference.generate, translateFormula, ihf both.1, ihl both.2,
        env₂, Inference.env₂, translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        fresh₀, fresh₁, Inference.fresh₀, Inference.fresh₁,
        lift₂, Inference.lift₂, CompTerm.var, Inference.CompTerm.var]
  | fst pair ih | snd pair ih =>
      simp [generate, Inference.generate, translateFormula, ih required,
        env₂, Inference.env₂, translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        fresh₀, fresh₁, Inference.fresh₀, Inference.fresh₁,
        lift₂, Inference.lift₂, CompTerm.var, Inference.CompTerm.var]
  | field label record ih | variant label payload ih =>
      simp [generate, Inference.generate, translateFormula, ih required,
        translateComp, CompTerm.rename, Inference.CompTerm.rename, translateType, eraseRow,
        CompTerm.var, Inference.CompTerm.var]

theorem principal_translation (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (schemes : SchemeEnv α) :
    translateFormula (principal schemes expression) = Inference.principal (translateEnv schemes) expression := by
  simp only [principal, Inference.principal, generate_translation expression required, env_lift, translate_var]

def translateAtom : Atom α → ConstraintNormalForm.Atom α
  | .tyLe source target => .tyLe (translateType source) (translateType target)
  | .rowLe source target => .rowLe (eraseRow source) (eraseRow target)

def translateClause (clause : Clause α) : ConstraintNormalForm.Clause α :=
  ⟨clause.locals, clause.atoms.map translateAtom⟩

@[simp] theorem atom_rename (rename : α → β) (atom : Atom α) :
    translateAtom (atom.rename rename) = (translateAtom atom).rename rename := by
  cases atom <;> simp [translateAtom, Atom.rename, ConstraintNormalForm.Atom.rename]

@[simp] theorem clause_empty : translateClause (Clause.empty : Clause α) = .empty := rfl

@[simp] theorem clause_singleton (atom : Atom α) :
    translateClause (Clause.singleton atom) = .singleton (translateAtom atom) := by
  simp [translateClause, Clause.singleton, ConstraintNormalForm.Clause.singleton]

@[simp] theorem clause_combine (first last : Clause α) :
    translateClause (first.combine last) = (translateClause first).combine (translateClause last) := by
  simp only [translateClause, Clause.combine, ConstraintNormalForm.Clause.combine,
    List.map_append, List.map_map, Function.comp_def, atom_rename]
  rfl

@[simp] theorem clause_close (clause : Clause (Option α)) :
    translateClause clause.close = (translateClause clause).close := by
  simp only [translateClause, Clause.close, ConstraintNormalForm.Clause.close,
    List.map_map, Function.comp_def, atom_rename]
  rfl

/-- The actual finite lists agree, rather than merely their satisfiability.
In particular every translated clause keeps the same number of local slots. -/
theorem normalise_translation (formula : Formula α) :
    (normalise formula).map translateClause = ConstraintNormalForm.normalise (translateFormula formula) := by
  induction formula with
  | top | bot | tyLe | rowLe =>
      simp [normalise, ConstraintNormalForm.normalise, translateFormula, translateAtom]
  | and first last ihf ihl =>
      simp only [normalise, translateFormula, ConstraintNormalForm.normalise]
      rw [← ihf, ← ihl]
      simp [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
  | or first last ihf ihl =>
      simp [normalise, ConstraintNormalForm.normalise, translateFormula, ihf, ihl]
  | existsSlot body ih =>
      simp only [normalise, translateFormula, ConstraintNormalForm.normalise, ← ih]
      simp [List.map_map, Function.comp_def]

@[simp] theorem clause_locals (clause : Clause α) : (translateClause clause).locals = clause.locals := rfl

theorem clause_pack (clause : Clause (Option Empty)) :
    clause.pack.map translateAtom = (translateClause clause).pack := by
  simp only [Clause.pack, ConstraintNormalForm.Clause.pack, translateClause,
    List.map_map, Function.comp_def, atom_rename]
  rfl

theorem clean_atom_translation (atom : Atom α) (good : CleanAtom atom) :
    eraseAtom atom = some (translateAtom atom) := by
  cases atom with
  | tyLe source target =>
      simp only [eraseAtom, clean_translation source good.1, clean_translation target good.2]
      rfl
  | rowLe => rfl

theorem clean_atoms_translation (atoms : List (Atom α)) (good : CleanAtoms atoms) :
    eraseAtoms atoms = some (atoms.map translateAtom) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      simp only [eraseAtoms, clean_atom_translation atom (good atom (List.mem_cons_self ..)),
        ih (fun item member => good item (List.mem_cons_of_mem _ member))]
      rfl

/-- Every presence clause of the same required-field source becomes an
actual clause of the unchanged old generator, at the original local IDs. -/
theorem generated_clause (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    translateClause clause ∈ ConstraintNormalForm.normalise
      (Inference.principal ([] : Inference.SchemeEnv Empty) expression) := by
  have mapped : translateClause clause ∈
      (normalise (principal ([] : SchemeEnv Empty) expression)).map translateClause :=
    List.mem_map.mpr ⟨clause, member, rfl⟩
  rw [normalise_translation, principal_translation expression required] at mapped
  exact mapped

theorem generated_pack_translation (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    eraseAtoms clause.pack = some (translateClause clause).pack := by
  rw [clean_atoms_translation clause.pack (generated_clean expression required clause member), clause_pack]
  rfl

/-- The old-supported boundary has no translation-success hypothesis. Its
actual old clause preserves every local computation slot, and its constraints
are exact for every single shared assignment of old regular values and rows. -/
theorem legacy_generated_clause_exact (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    translateClause clause ∈ ConstraintNormalForm.normalise
        (Inference.principal ([] : Inference.SchemeEnv Empty) expression) ∧
      eraseAtoms clause.pack = some (translateClause clause).pack ∧
      ∀ values : Fin (clause.locals + 1) → Inference.Comp CommonLegacyEmptyReflection.legacyModel,
        All Common.model (CommonLegacyTyping.assignment values) clause.pack ↔
          ConstraintNormalForm.All CommonLegacyEmptyReflection.contextualModel values (translateClause clause).pack := by
  have required := (Bool.and_eq_true_iff.mp supported).1
  have translated := generated_pack_translation expression required clause member
  exact ⟨generated_clause expression required clause member, translated,
    generated_atoms_exact expression clause member _ translated⟩

end Yulang.CommonLegacyGenerationTranslation
