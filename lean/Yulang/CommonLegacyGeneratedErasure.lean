import Yulang.CommonLegacyGeneratedAtoms

/-!+# Legacy erasure is defined on every generated required-field clause

The absence of whole-default constructors is preserved by renaming,
captured-scheme substitution, both value-let alternatives, normalization and
packing. Every old supported source therefore supplies the successful
`eraseAtoms` result internally. All original local slots are retained.

The resulting interpretation theorem still quantifies over shared legacy
assignments. It does not recover one from arbitrary common witnesses.
-/

namespace Yulang.CommonLegacyGeneratedErasure

open Core.PresenceGeneration PresenceNormalForm
open CommonLegacyGeneratedAtoms
open Inference (Expr)

def clean : TyTerm α → Bool
  | .recordDefault _ _ _ => false
  | .union first last | .inter first last | .pair first last
  | .record _ first last | .arrow first _ last _ => clean first && clean last
  | .required _ payload | .variant _ payload => clean payload
  | _ => true

def CleanComp (term : CompTerm α) : Prop := clean term.ty = true

def CleanFormula : Formula α → Prop
  | .top | .bot | .rowLe _ _ => True
  | .and first last | .or first last => CleanFormula first ∧ CleanFormula last
  | .tyLe first last => clean first = true ∧ clean last = true
  | .existsSlot body => CleanFormula body

def CleanEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, CleanFormula scheme

@[simp] theorem clean_rename (rename : α → β) (term : TyTerm α) :
    clean (term.rename rename) = clean term := by
  induction term <;> simp_all [TyTerm.rename, clean]

theorem CleanComp.rename {term : CompTerm α} (good : CleanComp term) (rename : α → β) :
    CleanComp (term.rename rename) := by simpa [CleanComp, CompTerm.rename] using good

theorem clean_var (index : α) : CleanComp (CompTerm.var index) := rfl

theorem clean_subst (subst : α → CompTerm β) (assignment : ∀ index, CleanComp (subst index))
    (term : TyTerm α) (good : clean term = true) : clean (term.subst subst) = true := by
  induction term <;> simp_all [clean, TyTerm.subst, CleanComp]

theorem CleanFormula.rename {formula : Formula α} (good : CleanFormula formula) (rename : α → β) :
    CleanFormula (formula.rename rename) := by
  induction formula generalizing β with
  | top | bot | rowLe => trivial
  | and _ _ ihf ihl | or _ _ ihf ihl => exact ⟨ihf good.1 rename, ihl good.2 rename⟩
  | tyLe => simpa [CleanFormula, Formula.rename] using good
  | existsSlot _ ih => exact ih good (Option.map rename)

theorem CleanFormula.subst {formula : Formula α} (good : CleanFormula formula)
    (subst : α → CompTerm β) (assignment : ∀ index, CleanComp (subst index)) :
    CleanFormula (formula.subst subst) := by
  induction formula generalizing β with
  | top | bot | rowLe => trivial
  | and _ _ ihf ihl | or _ _ ihf ihl =>
      exact ⟨ihf good.1 subst assignment, ihl good.2 subst assignment⟩
  | tyLe first last =>
      exact ⟨clean_subst subst assignment first good.1, clean_subst subst assignment last good.2⟩
  | existsSlot _ ih =>
      apply ih good (liftSubst subst)
      intro index
      cases index with
      | none => exact clean_var _
      | some index => exact (assignment index).rename some

theorem CleanEnv.rename {schemes : SchemeEnv α} (good : CleanEnv schemes) (rename : α → β) :
    CleanEnv (schemes.rename rename) := by
  intro scheme member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename (Option.map rename)

theorem CleanEnv.lift {schemes : SchemeEnv α} (good : CleanEnv schemes) : CleanEnv schemes.lift :=
  good.rename some

theorem CleanEnv.cons {schemes : SchemeEnv α} (good : CleanEnv schemes) {scheme : Scheme α}
    (head : CleanFormula scheme) : CleanEnv (scheme :: schemes) := by
  intro actual member
  exact (List.mem_cons.mp member).elim (fun same => same ▸ head) (good actual)

theorem clean_compLe {source target : CompTerm α} (first : CleanComp source) (last : CleanComp target) :
    CleanFormula (Formula.compLe source target) := ⟨⟨first, last⟩, trivial⟩

theorem clean_mono {term : CompTerm α} (good : CleanComp term) : CleanFormula (Scheme.mono term) :=
  clean_compLe (good.rename some) (clean_var none)

theorem CleanFormula.instantiate {scheme : Scheme α} (good : CleanFormula scheme)
    (output : CompTerm α) (accepted : CleanComp output) : CleanFormula (scheme.instantiate output) := by
  apply good.subst
  intro index
  cases index with
  | none => exact accepted
  | some index => exact clean_var _

theorem clean_lookup {schemes : SchemeEnv α} (good : CleanEnv schemes) (index : Nat)
    (output : CompTerm α) (accepted : CleanComp output) : CleanFormula (Scheme.lookup schemes index output) := by
  unfold Scheme.lookup
  cases found : schemes[index]? with
  | none => trivial
  | some scheme => exact (good scheme (List.mem_of_getElem? found)).instantiate output accepted

theorem clean_generate (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (schemes : SchemeEnv α) (environment : CleanEnv schemes)
    (output : CompTerm α) (accepted : CleanComp output) : CleanFormula (generate schemes expression output) := by
  induction expression generalizing α with
  | var index => exact clean_lookup environment index output accepted
  | lit scalar => exact clean_compLe rfl accepted
  | lam body ih =>
      exact ⟨ih required _ (environment.lift.lift.cons (clean_mono (clean_var _))) _ (clean_var _),
        clean_compLe rfl (accepted.rename _)⟩
  | app function argument ihf iha =>
      have both := Bool.and_eq_true_iff.mp required
      exact ⟨ihf both.1 _ environment.lift.lift.lift _ rfl,
        iha both.2 _ environment.lift.lift.lift _ (clean_var _), clean_compLe rfl (accepted.rename _)⟩
  | letE definition body ihd ihb =>
      have both := Bool.and_eq_true_iff.mp required
      have generalized : CleanFormula (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        ⟨ihd both.1 _ environment.lift _ rfl, trivial⟩
      have monomorphic : CleanFormula (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        ⟨ihd both.1 _ environment.lift.lift _ (clean_var _),
          ihb both.2 _ (environment.lift.lift.cons
            (clean_mono (term := CompTerm.pure (fresh₀ (α := α)).ty) rfl)) _ (clean_var _),
          clean_compLe rfl (accepted.rename _)⟩
      simp only [generate]
      split
      · exact ⟨⟨ihd both.1 _ environment.lift _ rfl,
          ihb both.2 _ (environment.cons generalized) output accepted⟩, monomorphic⟩
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      have both := Bool.and_eq_true_iff.mp required
      have first := Bool.and_eq_true_iff.mp both.1
      exact ⟨ihc first.1 _ environment.lift.lift.lift _ rfl,
        ihy first.2 _ environment.lift.lift.lift _ (clean_var _),
        ihn both.2 _ environment.lift.lift.lift _ (clean_var _), clean_compLe rfl (accepted.rename _)⟩
  | pair first last ihf ihl =>
      have both := Bool.and_eq_true_iff.mp required
      exact ⟨ihf both.1 _ environment.lift.lift _ (clean_var _),
        ihl both.2 _ environment.lift.lift _ (clean_var _), clean_compLe rfl (accepted.rename _)⟩
  | fst pair ih | snd pair ih =>
      exact ⟨ih required _ environment.lift.lift _ rfl, clean_compLe rfl (accepted.rename _)⟩
  | emptyRecord => exact clean_compLe rfl accepted
  | record label head rest ihh ihr =>
      have both := Bool.and_eq_true_iff.mp required
      exact ⟨ihh both.1 _ environment.lift.lift _ (clean_var _),
        ihr both.2 _ environment.lift.lift _ (clean_var _), ⟨rfl, rfl⟩,
        clean_compLe rfl (accepted.rename _)⟩
  | recordDefault => cases required
  | field label record ih =>
      exact ⟨ih required _ environment.lift _ rfl, clean_compLe rfl (accepted.rename _)⟩
  | variant label payload ih =>
      exact ⟨ih required _ environment.lift _ (clean_var _), clean_compLe rfl (accepted.rename _)⟩

theorem clean_principal (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (schemes : SchemeEnv α) (environment : CleanEnv schemes) : CleanFormula (principal schemes expression) :=
  clean_generate expression required schemes.lift environment.lift _ (clean_var none)

def CleanAtom : Atom α → Prop
  | .tyLe first last => clean first = true ∧ clean last = true
  | .rowLe _ _ => True

def CleanAtoms (atoms : List (Atom α)) : Prop := ∀ atom ∈ atoms, CleanAtom atom

def CleanClause (clause : Clause α) : Prop := CleanAtoms clause.atoms

theorem CleanAtom.rename {atom : Atom α} (good : CleanAtom atom) (rename : α → β) :
    CleanAtom (atom.rename rename) := by
  cases atom with
  | tyLe => simpa [CleanAtom, Atom.rename] using good
  | rowLe => trivial

theorem CleanAtoms.rename {atoms : List (Atom α)} (good : CleanAtoms atoms) (rename : α → β) :
    CleanAtoms (atoms.map (Atom.rename rename)) := by
  intro atom member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename rename

theorem CleanAtoms.append {first last : List (Atom α)} (left : CleanAtoms first) (right : CleanAtoms last) :
    CleanAtoms (first ++ last) := by
  intro atom member
  exact (List.mem_append.mp member).elim (left atom) (right atom)

theorem clean_empty : CleanClause (Clause.empty : Clause α) := by intro atom impossible; cases impossible

theorem clean_singleton {atom : Atom α} (good : CleanAtom atom) : CleanClause (Clause.singleton atom) := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  exact good.rename Sum.inr

theorem CleanClause.combine {first last : Clause α} (left : CleanClause first) (right : CleanClause last) :
    CleanClause (first.combine last) :=
  (left.rename (leftName first.locals last.locals)).append
    (right.rename (rightName first.locals last.locals))

theorem CleanClause.close {clause : Clause (Option α)} (good : CleanClause clause) : CleanClause clause.close :=
  good.rename (closeName clause.locals)

theorem clean_normalise {formula : Formula α} (good : CleanFormula formula) :
    ∀ clause ∈ normalise formula, CleanClause clause := by
  induction formula with
  | top =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact clean_empty
  | bot => intro clause impossible; cases impossible
  | tyLe | rowLe =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact clean_singleton good
  | and first last ihf ihl =>
      intro clause member
      obtain ⟨left, included, member⟩ := List.mem_flatMap.mp member
      obtain ⟨right, present, rfl⟩ := List.mem_map.mp member
      exact (ihf good.1 left included).combine (ihl good.2 right present)
  | or first last ihf ihl =>
      intro clause member
      exact (List.mem_append.mp member).elim (ihf good.1 clause) (ihl good.2 clause)
  | existsSlot formula ih =>
      intro clause member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (ih good original present).close

theorem generated_clean (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) : CleanAtoms clause.pack :=
  (clean_normalise (clean_principal expression required []
    (by intro _ impossible; cases impossible)) clause member).rename (resultName clause.locals)

theorem clean_erases (term : TyTerm α) (good : clean term = true) : ∃ erased, eraseType term = some erased := by
  induction term with
  | var | base | bottom | top | emptyRecord | exactEmpty => exact ⟨_, rfl⟩
  | union first last ihf ihl | inter first last ihf ihl | pair first last ihf ihl
  | record _ first last ihf ihl | arrow first _ last _ ihf ihl =>
      have both := Bool.and_eq_true_iff.mp good
      obtain ⟨a, ha⟩ := ihf both.1
      obtain ⟨b, hb⟩ := ihl both.2
      exact ⟨_, by simp [eraseType, ha, hb]; rfl⟩
  | required label payload ih | variant label payload ih =>
      obtain ⟨erased, found⟩ := ih good
      exact ⟨_, by simp [eraseType, found]; rfl⟩
  | recordDefault => cases good

theorem CleanAtom.erases (atom : Atom α) (good : CleanAtom atom) : ∃ erased, eraseAtom atom = some erased := by
  cases atom with
  | rowLe => exact ⟨_, rfl⟩
  | tyLe first last =>
      obtain ⟨a, ha⟩ := clean_erases first good.1
      obtain ⟨b, hb⟩ := clean_erases last good.2
      exact ⟨_, by simp [eraseAtom, ha, hb]; rfl⟩

theorem CleanAtoms.erases (atoms : List (Atom α)) (good : CleanAtoms atoms) :
    ∃ erased, eraseAtoms atoms = some erased := by
  induction atoms with
  | nil => exact ⟨_, rfl⟩
  | cons atom atoms ih =>
      obtain ⟨head, first⟩ := CleanAtom.erases atom (good atom (List.mem_cons_self ..))
      obtain ⟨tail, last⟩ := ih (fun item member => good item (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, by simp [eraseAtoms, first, last]⟩

/-- Erasure cannot fail for any clause returned from a required-field source,
before any semantic values or rows have been chosen. -/
theorem generated_erases (expression : Expr) (required : expression.requiredFieldsOnly = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    ∃ erased, eraseAtoms clause.pack = some erased :=
  CleanAtoms.erases clause.pack (generated_clean expression required clause member)

/-- Every old supported expression supplies successful erasure internally.
The returned finite conjunction is exact for all shared old assignments. -/
theorem legacy_generated_exact (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) :
    ∃ erased, eraseAtoms clause.pack = some erased ∧
      ∀ values : Fin (clause.locals + 1) → Inference.Comp CommonLegacyEmptyReflection.legacyModel,
        All Common.model (CommonLegacyTyping.assignment values) clause.pack ↔
          ConstraintNormalForm.All CommonLegacyEmptyReflection.contextualModel values erased := by
  have required := (Bool.and_eq_true_iff.mp supported).1
  obtain ⟨erased, translated⟩ := generated_erases expression required clause member
  exact ⟨erased, translated, generated_atoms_exact expression clause member erased translated⟩

end Yulang.CommonLegacyGeneratedErasure
