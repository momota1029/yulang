import Yulang.PresenceNormalForm

/-!
# The rigid endpoint grammar of every generated presence clause

The actual source generator puts a variable, base, pair, arrow, required
field, or width record at an upper endpoint. A lower endpoint may additionally
be a union; recursively removing its union heads never exposes an intersection.
These are properties of syntax, not restrictions on any value assigned to a
slot. In particular every result slot can still denote an arbitrary common
type, and every arrow child can still denote an arbitrary regular type.

The invariants survive captured scheme substitution, both alternatives of a
value let, all source constructors, normalization and binder packing. This
allows the symbolic inspector to cover all actual generated clauses without
claiming a false general decomposition of source intersections or target
unions into alternatives of ordinary child comparisons.
-/

namespace Yulang.PresenceGeneratedRigidShape

open Core.PresenceGeneration PresenceNormalForm
open Inference (Expr)

def upper : TyTerm α → Bool
  | .var _ | .base _ | .pair _ _ | .arrow _ _ _ _ | .required _ _ | .emptyRecord => true
  | _ => false

def lower : TyTerm α → Bool
  | .union first last => lower first && lower last
  | .inter _ _ => false
  | _ => true

theorem upper_lower (term : TyTerm α) (accepted : upper term = true) : lower term = true := by
  cases term <;> first | rfl | cases accepted

def GoodComp (term : CompTerm α) : Prop := upper term.ty = true

def GoodFormula : Formula α → Prop
  | .top | .bot | .rowLe _ _ => True
  | .and first last | .or first last => GoodFormula first ∧ GoodFormula last
  | .tyLe first last => lower first = true ∧ upper last = true
  | .existsSlot formula => GoodFormula formula

def GoodEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, GoodFormula scheme

@[simp] theorem upper_rename (rename : α → β) (term : TyTerm α) :
    upper (term.rename rename) = upper term := by cases term <;> rfl

@[simp] theorem lower_rename (rename : α → β) (term : TyTerm α) :
    lower (term.rename rename) = lower term := by
  induction term <;> simp_all [TyTerm.rename, lower]

theorem GoodComp.rename {term : CompTerm α} (good : GoodComp term) (rename : α → β) :
    GoodComp (term.rename rename) := by simpa [GoodComp, CompTerm.rename] using good

theorem good_var (index : α) : GoodComp (CompTerm.var index) := rfl

theorem upper_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : upper term = true) : upper (term.subst subst) = true := by
  cases term with
  | var index => exact assignment index
  | base | pair | arrow | required | emptyRecord => rfl
  | _ => cases good

theorem lower_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) (good : lower term = true) : lower (term.subst subst) = true := by
  induction term with
  | var index => exact upper_lower _ (assignment index)
  | union first last ihf ihl =>
      have both := Bool.and_eq_true_iff.mp good
      exact Bool.and_eq_true_iff.mpr ⟨ihf both.1, ihl both.2⟩
  | inter => cases good
  | _ => rfl

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
theorem generated_endpoint_shapes (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) : GoodAtoms clause.pack :=
  good_pack (good_normalise (good_principal expression []
    (by intro _ impossible; cases impossible)) clause member)

theorem generated_core_endpoint_shapes (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)) :
    GoodAtoms clause.pack := by
  cases supported : Core.InferenceSyntax.supported expression with
  | false =>
      simp only [CoreRules.principalCore, CoreRules.generateCore, supported,
        Bool.false_eq_true, ↓reduceIte, normalise, List.not_mem_nil] at member
  | true =>
      apply generated_endpoint_shapes (CoreRules.decode expression) clause
      simpa only [CoreRules.principalCore, CoreRules.generateCore, supported, ↓reduceIte, principal]
        using member

end Yulang.PresenceGeneratedRigidShape
