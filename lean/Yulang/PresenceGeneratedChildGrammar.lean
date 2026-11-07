import Yulang.PresenceGeneratedRigidShape

/-!
# Recursive child grammar of every generated presence clause

Every upper endpoint is recursively built from variables, bases, pairs,
arrows, required fields and width records. A lower endpoint may additionally
have a union, variant, exact-record, whole record/default or lattice-constant
head, but each proper child is again in the recursive upper grammar.

These are properties of original generated syntax, preserved through captured
scheme substitution, both value-let alternatives, normalization and packing.
They place no restriction on the common types assigned to variables. In
particular a negative arrow child may denote an arbitrary common union or
regular graph while its original shared node remains in this finite grammar.
-/

namespace Yulang.PresenceGeneratedChildGrammar

open Core.PresenceGeneration PresenceNormalForm
open Inference (Expr)

def upper : TyTerm α → Bool
  | .var _ | .base _ | .emptyRecord => true
  | .pair first last | .arrow first _ last _ => upper first && upper last
  | .required _ payload => upper payload
  | _ => false

def lower : TyTerm α → Bool
  | .inter _ _ => false
  | .union first last | .pair first last | .arrow first _ last _
  | .record _ first last | .recordDefault _ first last => upper first && upper last
  | .required _ payload | .variant _ payload => upper payload
  | _ => true

theorem upper_lower (term : TyTerm α) (accepted : upper term = true) : lower term = true := by
  cases term <;> first | exact accepted | rfl | cases accepted

def GoodComp (term : CompTerm α) : Prop := upper term.ty = true

def GoodFormula : Formula α → Prop
  | .top | .bot | .rowLe _ _ => True
  | .and first last | .or first last => GoodFormula first ∧ GoodFormula last
  | .tyLe first last => lower first = true ∧ upper last = true
  | .existsSlot formula => GoodFormula formula

def GoodEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, GoodFormula scheme

@[simp] theorem upper_rename (rename : α → β) (term : TyTerm α) :
    upper (term.rename rename) = upper term := by
  induction term <;> simp_all [TyTerm.rename, upper]

@[simp] theorem lower_rename (rename : α → β) (term : TyTerm α) :
    lower (term.rename rename) = lower term := by
  cases term <;> simp [TyTerm.rename, lower]

theorem GoodComp.rename {term : CompTerm α} (good : GoodComp term) (rename : α → β) :
    GoodComp (term.rename rename) := by simpa [GoodComp, CompTerm.rename] using good

theorem good_var (index : α) : GoodComp (CompTerm.var index) := rfl

theorem upper_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : upper term = true) : upper (term.subst subst) = true := by
  induction term <;> simp_all [upper, TyTerm.subst, GoodComp]

theorem lower_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : lower term = true) : lower (term.subst subst) = true := by
  cases term
  case var index => exact upper_lower _ (assignment index)
  all_goals simp only [lower, TyTerm.subst] at good ⊢
  all_goals try exact good
  all_goals try rfl
  all_goals try exact upper_subst subst assignment _ good
  all_goals
    have both := Bool.and_eq_true_iff.mp good
    exact Bool.and_eq_true_iff.mpr ⟨upper_subst subst assignment _ both.1,
      upper_subst subst assignment _ both.2⟩

theorem GoodFormula.rename {formula : Formula α} (good : GoodFormula formula) (rename : α → β) :
    GoodFormula (formula.rename rename) := by
  induction formula generalizing β with
  | top | bot | rowLe => trivial
  | and _ _ ihf ihl | or _ _ ihf ihl => exact ⟨ihf good.1 rename, ihl good.2 rename⟩
  | tyLe => simpa [GoodFormula, Formula.rename] using good
  | existsSlot formula ih => exact ih good (Option.map rename)

theorem GoodFormula.subst {formula : Formula α} (good : GoodFormula formula) (subst : α → CompTerm β)
    (assignment : ∀ index, GoodComp (subst index)) : GoodFormula (formula.subst subst) := by
  induction formula generalizing β with
  | top | bot | rowLe => trivial
  | and _ _ ihf ihl | or _ _ ihf ihl =>
      exact ⟨ihf good.1 subst assignment, ihl good.2 subst assignment⟩
  | tyLe first last => exact ⟨lower_subst subst assignment first good.1,
      upper_subst subst assignment last good.2⟩
  | existsSlot formula ih =>
      apply ih good (liftSubst subst)
      intro index
      cases index with
      | none => exact good_var _
      | some index => exact (assignment index).rename some

theorem GoodEnv.rename {schemes : SchemeEnv α} (good : GoodEnv schemes) (rename : α → β) :
    GoodEnv (schemes.rename rename) := by
  intro scheme member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename (Option.map rename)

theorem GoodEnv.lift {schemes : SchemeEnv α} (good : GoodEnv schemes) : GoodEnv schemes.lift :=
  good.rename some

theorem GoodEnv.cons {schemes : SchemeEnv α} (good : GoodEnv schemes) {scheme : Scheme α}
    (head : GoodFormula scheme) : GoodEnv (scheme :: schemes) := by
  intro actual member
  exact (List.mem_cons.mp member).elim (fun same => same ▸ head) (good actual)

theorem good_compLe {source target : CompTerm α}
    (first : lower source.ty = true) (last : GoodComp target) : GoodFormula (Formula.compLe source target) :=
  ⟨⟨first, last⟩, trivial⟩

theorem good_mono {term : CompTerm α} (good : GoodComp term) : GoodFormula (Scheme.mono term) :=
  good_compLe (upper_lower _ (good.rename some)) (good_var none)

theorem GoodFormula.instantiate {scheme : Scheme α} (good : GoodFormula scheme)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (scheme.instantiate output) := by
  apply good.subst
  intro index
  cases index with
  | none => exact accepted
  | some index => exact good_var _

theorem good_lookup {schemes : SchemeEnv α} (good : GoodEnv schemes) (index : Nat)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (Scheme.lookup schemes index output) := by
  unfold Scheme.lookup
  cases found : schemes[index]? with
  | none => trivial
  | some scheme => exact (good scheme (List.mem_of_getElem? found)).instantiate output accepted

/-- Every original source expression preserves the endpoint grammar. This
includes scheme instantiation and both alternatives of a value-restricted let. -/
theorem good_generate (expression : Expr)
    (schemes : SchemeEnv α) (environment : GoodEnv schemes)
    (output : CompTerm α) (accepted : GoodComp output) : GoodFormula (generate schemes expression output) := by
  induction expression generalizing α with
  | var index => exact good_lookup environment index output accepted
  | lit scalar => exact good_compLe rfl accepted
  | lam body ih =>
      exact ⟨ih _ (environment.lift.lift.cons (good_mono (good_var _))) _ (good_var _),
        good_compLe rfl (accepted.rename _)⟩
  | app function argument ihf iha =>
      exact ⟨ihf _ environment.lift.lift.lift _ rfl,
        iha _ environment.lift.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | letE definition body ihd ihb =>
      have generalized : GoodFormula (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        ⟨ihd _ environment.lift _ rfl, trivial⟩
      have monomorphic : GoodFormula (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        ⟨ihd _ environment.lift.lift _ (good_var _),
          ihb _ (environment.lift.lift.cons
            (good_mono (term := CompTerm.pure (fresh₀ (α := α)).ty) rfl)) _ (good_var _),
          good_compLe rfl (accepted.rename _)⟩
      simp only [generate]
      split
      · exact ⟨⟨ihd _ environment.lift _ rfl,
          ihb _ (environment.cons generalized) output accepted⟩, monomorphic⟩
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      exact ⟨ihc _ environment.lift.lift.lift _ rfl,
        ihy _ environment.lift.lift.lift _ (good_var _),
        ihn _ environment.lift.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | pair first last ihf ihl =>
      exact ⟨ihf _ environment.lift.lift _ (good_var _),
        ihl _ environment.lift.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩
  | fst pair ih | snd pair ih =>
      exact ⟨ih _ environment.lift.lift _ rfl, good_compLe rfl (accepted.rename _)⟩
  | emptyRecord => exact good_compLe rfl accepted
  | record label head rest ihh ihr | recordDefault label head rest ihh ihr =>
      exact ⟨ihh _ environment.lift.lift _ (good_var _),
        ihr _ environment.lift.lift _ (good_var _), ⟨rfl, rfl⟩,
        good_compLe rfl (accepted.rename _)⟩
  | field label record ih =>
      exact ⟨ih _ environment.lift _ rfl, good_compLe rfl (accepted.rename _)⟩
  | variant label payload ih =>
      exact ⟨ih _ environment.lift _ (good_var _), good_compLe rfl (accepted.rename _)⟩

theorem good_principal (expression : Expr)
    (schemes : SchemeEnv α) (environment : GoodEnv schemes) : GoodFormula (principal schemes expression) :=
  good_generate expression schemes.lift environment.lift _ (good_var none)

def GoodAtom : Atom α → Prop
  | .tyLe first last => lower first = true ∧ upper last = true
  | .rowLe _ _ => True

def GoodAtoms (atoms : List (Atom α)) : Prop := ∀ atom ∈ atoms, GoodAtom atom

def GoodClause (clause : Clause α) : Prop := GoodAtoms clause.atoms

theorem GoodAtom.rename {atom : Atom α} (good : GoodAtom atom) (rename : α → β) :
    GoodAtom (atom.rename rename) := by
  cases atom with
  | tyLe => simpa [GoodAtom, Atom.rename] using good
  | rowLe => trivial

theorem GoodAtoms.rename {atoms : List (Atom α)} (good : GoodAtoms atoms) (rename : α → β) :
    GoodAtoms (atoms.map (Atom.rename rename)) := by
  intro atom member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename rename

theorem GoodAtoms.append {first last : List (Atom α)} (left : GoodAtoms first) (right : GoodAtoms last) :
    GoodAtoms (first ++ last) := by
  intro atom member
  exact (List.mem_append.mp member).elim (left atom) (right atom)

theorem good_empty : GoodClause (Clause.empty : Clause α) := by intro atom impossible; cases impossible

theorem good_singleton {atom : Atom α} (good : GoodAtom atom) : GoodClause (Clause.singleton atom) := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  exact good.rename Sum.inr

theorem GoodClause.combine {first last : Clause α} (left : GoodClause first) (right : GoodClause last) :
    GoodClause (first.combine last) :=
  (left.rename (leftName first.locals last.locals)).append
    (right.rename (rightName first.locals last.locals))

theorem GoodClause.close {clause : Clause (Option α)} (good : GoodClause clause) : GoodClause clause.close :=
  good.rename (closeName clause.locals)

theorem good_normalise {formula : Formula α} (good : GoodFormula formula) :
    ∀ clause ∈ normalise formula, GoodClause clause := by
  induction formula with
  | top =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact good_empty
  | bot => intro clause impossible; cases impossible
  | tyLe | rowLe =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      exact good_singleton good
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

theorem good_pack {clause : Clause (Option Empty)} (good : GoodClause clause) : GoodAtoms clause.pack :=
  good.rename (resultName clause.locals)

/-- The endpoint grammar holds for every clause of every closed source
expression. No source-support or solver-success condition is required. -/
theorem generated_child_grammar (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) : GoodAtoms clause.pack :=
  good_pack (good_normalise (good_principal expression []
    (by intro _ impossible; cases impossible)) clause member)

theorem generated_core_child_grammar (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)) :
    GoodAtoms clause.pack := by
  cases supported : Core.InferenceSyntax.supported expression with
  | false =>
      simp only [CoreRules.principalCore, CoreRules.generateCore, supported,
        Bool.false_eq_true, ↓reduceIte, normalise, List.not_mem_nil] at member
  | true =>
      apply generated_child_grammar (CoreRules.decode expression) clause
      simpa only [CoreRules.principalCore, CoreRules.generateCore, supported, ↓reduceIte, principal]
        using member

theorem upper_head (term : TyTerm α) (good : upper term = true) :
    PresenceGeneratedRigidShape.upper term = true := by
  cases term <;> first | rfl | cases good

theorem lower_head (term : TyTerm α) (good : lower term = true) :
    PresenceGeneratedRigidShape.lower term = true := by
  cases term
  case union first last =>
    have both := Bool.and_eq_true_iff.mp good
    exact Bool.and_eq_true_iff.mpr
      ⟨PresenceGeneratedRigidShape.upper_lower first (upper_head first both.1),
        PresenceGeneratedRigidShape.upper_lower last (upper_head last both.2)⟩
  case inter => cases good
  all_goals rfl

end Yulang.PresenceGeneratedChildGrammar
