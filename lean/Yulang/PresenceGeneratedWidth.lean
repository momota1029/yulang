import Yulang.PresenceGeneratedChildGrammar

/-!
# Width atoms accompanying generated record and default heads

The invariant records an actual atom in the same finite clause. It does not
assume record shape of an unknown value. A syntactic derivation marks the
generator's paired width/head constraints and survives arbitrary renaming,
capture-avoiding substitution by the generated upper grammar, normalization,
and binder packing.
-/

namespace Yulang.PresenceGeneratedWidth

open Core.PresenceGeneration PresenceNormalForm
open PresenceGeneratedChildGrammar (upper GoodComp good_var)
open Inference (Expr)

def widthTail : TyTerm α → Option (TyTerm α)
  | .record _ _ tail => some tail
  | .recordDefault _ source _ => some source
  | _ => none

theorem upper_no_width (term : TyTerm α) (good : upper term = true) : widthTail term = none := by
  cases term <;> first | rfl | cases good

@[simp] theorem widthTail_rename (rename : α → β) (term : TyTerm α) :
    widthTail (term.rename rename) = (widthTail term).map (TyTerm.rename rename) := by
  cases term <;> rfl

theorem widthTail_subst (subst : α → CompTerm β) (assignment : ∀ index, GoodComp (subst index))
    (term : TyTerm α) :
    widthTail (term.subst subst) = (widthTail term).map (TyTerm.subst subst) := by
  cases term with
  | var index => exact upper_no_width _ (assignment index)
  | _ => rfl

def WidthAtoms (atoms : List (Atom α)) : Prop :=
  ∀ source target, .tyLe source target ∈ atoms →
    ∀ tail, widthTail source = some tail → .tyLe tail .emptyRecord ∈ atoms

def WidthClause (clause : Clause α) : Prop := WidthAtoms clause.atoms

theorem WidthAtoms.rename {atoms : List (Atom α)} (good : WidthAtoms atoms) (rename : α → β) :
    WidthAtoms (atoms.map (Atom.rename rename)) := by
  intro source target member tail needed
  obtain ⟨atom, included, equal⟩ := List.mem_map.mp member
  cases atom with
  | rowLe => cases equal
  | tyLe first last =>
      cases equal
      rw [widthTail_rename] at needed
      obtain ⟨previous, found, rfl⟩ := Option.map_eq_some_iff.mp needed
      exact List.mem_map.mpr ⟨.tyLe previous .emptyRecord,
        good first last included previous found, rfl⟩

theorem WidthAtoms.append {first last : List (Atom α)} (left : WidthAtoms first)
    (right : WidthAtoms last) : WidthAtoms (first ++ last) := by
  intro source target member tail needed
  rcases List.mem_append.mp member with before | after
  · exact List.mem_append_left _ (left source target before tail needed)
  · exact List.mem_append_right _ (right source target after tail needed)

theorem WidthClause.combine {first last : Clause α} (left : WidthClause first)
    (right : WidthClause last) : WidthClause (first.combine last) :=
  (left.rename (leftName first.locals last.locals)).append
    (right.rename (rightName first.locals last.locals))

theorem WidthClause.close {clause : Clause (Option α)} (good : WidthClause clause) :
    WidthClause clause.close := good.rename (closeName clause.locals)

/-- A purely syntactic certificate for retaining paired atoms. The width
constructor requires only the generated upper syntax of the tail itself. -/
inductive Guarded : {α : Type} → Formula α → Prop where
  | top : Guarded (.top : Formula α)
  | bot : Guarded (.bot : Formula α)
  | rowLe (first last : RowTerm α) : Guarded (.rowLe first last)
  | tyLe (first last : TyTerm α) (none : widthTail first = none) : Guarded (.tyLe first last)
  | and {first last : Formula α} : Guarded first → Guarded last → Guarded (.and first last)
  | or {first last : Formula α} : Guarded first → Guarded last → Guarded (.or first last)
  | existsSlot {formula : Formula (Option α)} : Guarded formula → Guarded (.existsSlot formula)
  | width (source target : CompTerm α) (tail : TyTerm α)
      (needed : widthTail source.ty = some tail) (upperTail : upper tail = true) :
      Guarded (.and (.tyLe tail .emptyRecord) (Formula.compLe source target))

theorem Guarded.rename {formula : Formula α} (good : Guarded formula) (rename : α → β) :
    Guarded (formula.rename rename) := by
  induction good generalizing β with
  | top => exact .top
  | bot => exact .bot
  | rowLe => exact .rowLe _ _
  | tyLe first last none =>
      exact .tyLe _ _ (by simp only [widthTail_rename, none, Option.map_none])
  | and _ _ before after => exact .and (before rename) (after rename)
  | or _ _ before after => exact .or (before rename) (after rename)
  | existsSlot _ ih => exact .existsSlot (ih (Option.map rename))
  | width source target tail needed upperTail =>
      apply Guarded.width (source.rename rename) (target.rename rename) (tail.rename rename)
      · simp only [CompTerm.rename, widthTail_rename, needed, Option.map_some]
      · simpa only [PresenceGeneratedChildGrammar.upper_rename] using upperTail

theorem Guarded.subst {formula : Formula α} (good : Guarded formula) (subst : α → CompTerm β)
    (assignment : ∀ index, GoodComp (subst index)) : Guarded (formula.subst subst) := by
  induction good generalizing β with
  | top => exact .top
  | bot => exact .bot
  | rowLe => exact .rowLe _ _
  | tyLe first last none =>
      exact .tyLe _ _ (by simp only [widthTail_subst subst assignment, none, Option.map_none])
  | and _ _ before after => exact .and (before subst assignment) (after subst assignment)
  | or _ _ before after => exact .or (before subst assignment) (after subst assignment)
  | existsSlot _ ih =>
      apply Guarded.existsSlot
      apply ih (liftSubst subst)
      intro index
      cases index with
      | none => exact good_var _
      | some index => exact (assignment index).rename some
  | width source target tail needed upperTail =>
      apply Guarded.width (source.subst subst) (target.subst subst) (tail.subst subst)
      · simp only [CompTerm.subst, widthTail_subst subst assignment, needed, Option.map_some]
      · exact PresenceGeneratedChildGrammar.upper_subst subst assignment tail upperTail

private theorem row_rename_comp (first : α → β) (last : β → γ) (term : RowTerm α) :
    (term.rename first).rename last = term.rename (last ∘ first) := by
  induction term <;> simp_all [RowTerm.rename]

private theorem ty_rename_comp (first : α → β) (last : β → γ) (term : TyTerm α) :
    (term.rename first).rename last = term.rename (last ∘ first) := by
  induction term <;> simp_all [TyTerm.rename, row_rename_comp]

private theorem normalise_width (source target : CompTerm α) (tail : TyTerm α) :
    normalise (.and (.tyLe tail .emptyRecord) (Formula.compLe source target)) =
      [⟨0, ([.tyLe tail .emptyRecord, .tyLe source.ty target.ty, .rowLe source.row target.row] :
        List (Atom α)).map (Atom.rename Sum.inr)⟩] := by
  simp [normalise, Formula.compLe, Clause.singleton, Clause.combine, Atom.rename,
    ty_rename_comp, row_rename_comp, Function.comp_def, leftName, rightName]

private theorem width_atoms (source target : CompTerm α) (tail : TyTerm α)
    (needed : widthTail source.ty = some tail) (upperTail : upper tail = true) :
    WidthAtoms [.tyLe tail .emptyRecord, .tyLe source.ty target.ty, .rowLe source.row target.row] := by
  intro first last member actual needs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · cases equal
    rw [upper_no_width tail upperTail] at needs
    cases needs
  · cases equal
    have same : tail = actual := Option.some.inj (needed.symm.trans needs)
    subst actual
    exact List.mem_cons_self
  · cases equal

theorem guarded_normalise {formula : Formula α} (good : Guarded formula) :
    ∀ clause ∈ normalise formula, WidthClause clause := by
  induction good with
  | top =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      intro _ _ impossible
      cases impossible
  | bot => intro _ impossible; cases impossible
  | rowLe first last =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      change WidthAtoms ([Atom.rowLe first last].map (Atom.rename Sum.inr))
      apply WidthAtoms.rename
      intro _ _ impossible
      have same := List.mem_singleton.mp impossible
      cases same
  | tyLe first last none =>
      intro clause member
      have same := List.mem_singleton.mp member
      subst clause
      change WidthAtoms ([Atom.tyLe first last].map (Atom.rename Sum.inr))
      apply WidthAtoms.rename
      intro actual target included tail needed
      have same := List.mem_singleton.mp included
      cases same
      rw [none] at needed
      cases needed
  | and _ _ before after =>
      intro clause member
      obtain ⟨left, included, member⟩ := List.mem_flatMap.mp member
      obtain ⟨right, present, rfl⟩ := List.mem_map.mp member
      exact (before left included).combine (after right present)
  | or _ _ before after =>
      intro clause member
      exact (List.mem_append.mp member).elim (before clause) (after clause)
  | existsSlot _ ih =>
      intro clause member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (ih original present).close
  | width source target tail needed upperTail =>
      intro clause member
      rw [normalise_width] at member
      have same := List.mem_singleton.mp member
      subst clause
      exact (width_atoms source target tail needed upperTail).rename Sum.inr

theorem WidthClause.pack {clause : Clause (Option Empty)} (good : WidthClause clause) :
    WidthAtoms clause.pack := good.rename (resultName clause.locals)

def GuardedEnv (schemes : SchemeEnv α) : Prop := ∀ scheme ∈ schemes, Guarded scheme

theorem GuardedEnv.rename {schemes : SchemeEnv α} (good : GuardedEnv schemes) (rename : α → β) :
    GuardedEnv (schemes.rename rename) := by
  intro scheme member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename (Option.map rename)

theorem GuardedEnv.lift {schemes : SchemeEnv α} (good : GuardedEnv schemes) : GuardedEnv schemes.lift :=
  good.rename some

theorem GuardedEnv.cons {schemes : SchemeEnv α} (good : GuardedEnv schemes) {scheme : Scheme α}
    (head : Guarded scheme) : GuardedEnv (scheme :: schemes) := by
  intro actual member
  exact (List.mem_cons.mp member).elim (fun same => same ▸ head) (good actual)

theorem guarded_compLe {source target : CompTerm α} (none : widthTail source.ty = none) :
    Guarded (Formula.compLe source target) :=
  .and (.tyLe source.ty target.ty none) (.rowLe source.row target.row)

theorem guarded_mono {term : CompTerm α} (good : GoodComp term) : Guarded (Scheme.mono term) :=
  guarded_compLe (upper_no_width _ (good.rename some))

theorem Guarded.instantiate {scheme : Scheme α} (good : Guarded scheme)
    (output : CompTerm α) (accepted : GoodComp output) : Guarded (scheme.instantiate output) := by
  apply good.subst
  intro index
  cases index with
  | none => exact accepted
  | some index => exact good_var _

theorem guarded_lookup {schemes : SchemeEnv α} (good : GuardedEnv schemes) (index : Nat)
    (output : CompTerm α) (accepted : GoodComp output) : Guarded (Scheme.lookup schemes index output) := by
  unfold Scheme.lookup
  cases found : schemes[index]? with
  | none => exact .bot
  | some scheme => exact (good scheme (List.mem_of_getElem? found)).instantiate output accepted

/-- Every source constructor keeps the width atom paired with its record or
default lower endpoint, including both value-let alternatives and captured
scheme instantiation. -/
theorem guarded_generate (expression : Expr)
    (schemes : SchemeEnv α) (environment : GuardedEnv schemes)
    (output : CompTerm α) (accepted : GoodComp output) : Guarded (generate schemes expression output) := by
  induction expression generalizing α with
  | var index => exact guarded_lookup environment index output accepted
  | lit scalar => exact guarded_compLe rfl
  | lam body ih =>
      exact .existsSlot (.existsSlot (.and
        (ih _ (environment.lift.lift.cons (guarded_mono (good_var _))) _ (good_var _))
        (guarded_compLe rfl)))
  | app function argument ihf iha =>
      exact .existsSlot (.existsSlot (.existsSlot (.and
        (ihf _ environment.lift.lift.lift _ rfl)
        (.and (iha _ environment.lift.lift.lift _ (good_var _)) (guarded_compLe rfl)))))
  | letE definition body ihd ihb =>
      have generalized : Guarded (.and
          (generate schemes.lift definition (CompTerm.pure (.var none))) (.rowLe .empty (.var none))) :=
        .and (ihd _ environment.lift _ rfl) (.rowLe _ _)
      have monomorphic : Guarded (.existsSlot (.existsSlot (
          .and (generate (env₂ schemes) definition fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ schemes) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ output)))))) :=
        .existsSlot (.existsSlot (.and (ihd _ environment.lift.lift _ (good_var _))
          (.and (ihb _ (environment.lift.lift.cons
            (guarded_mono (term := CompTerm.pure (fresh₀ (α := α)).ty) rfl)) _ (good_var _))
            (guarded_compLe rfl))))
      simp only [generate]
      split
      · exact .or (.and (.existsSlot (ihd _ environment.lift _ rfl))
          (ihb _ (environment.cons generalized) output accepted)) monomorphic
      · exact monomorphic
  | branch condition yes no ihc ihy ihn =>
      exact .existsSlot (.existsSlot (.existsSlot (.and
        (ihc _ environment.lift.lift.lift _ rfl)
        (.and (ihy _ environment.lift.lift.lift _ (good_var _))
          (.and (ihn _ environment.lift.lift.lift _ (good_var _)) (guarded_compLe rfl))))))
  | pair first last ihf ihl =>
      exact .existsSlot (.existsSlot (.and (ihf _ environment.lift.lift _ (good_var _))
        (.and (ihl _ environment.lift.lift _ (good_var _)) (guarded_compLe rfl))))
  | fst pair ih | snd pair ih =>
      exact .existsSlot (.existsSlot (.and (ih _ environment.lift.lift _ rfl) (guarded_compLe rfl)))
  | emptyRecord => exact guarded_compLe rfl
  | record label head rest ihh ihr =>
      exact .existsSlot (.existsSlot (.and (ihh _ environment.lift.lift _ (good_var _))
        (.and (ihr _ environment.lift.lift _ (good_var _)) (.width _ _ fresh₁.ty rfl rfl))))
  | recordDefault label source fallback ihs ihf =>
      exact .existsSlot (.existsSlot (.and (ihs _ environment.lift.lift _ (good_var _))
        (.and (ihf _ environment.lift.lift _ (good_var _)) (.width _ _ fresh₀.ty rfl rfl))))
  | field label record ih =>
      exact .existsSlot (.and (ih _ environment.lift _ rfl) (guarded_compLe rfl))
  | variant label payload ih =>
      exact .existsSlot (.and (ih _ environment.lift _ (good_var _)) (guarded_compLe rfl))

theorem guarded_principal (expression : Expr) (schemes : SchemeEnv α)
    (environment : GuardedEnv schemes) : Guarded (principal schemes expression) :=
  guarded_generate expression schemes.lift environment.lift _ (good_var none)

/-- Every actual closed source clause contains the width atom required by
each of its record/default lower roots. There is no support or solver premise. -/
theorem generated_width_atoms (expression : Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)) : WidthAtoms clause.pack :=
  (guarded_normalise (guarded_principal expression [] (by intro _ impossible; cases impossible))
    clause member).pack

theorem generated_core_width_atoms (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)) :
    WidthAtoms clause.pack := by
  cases supported : Core.InferenceSyntax.supported expression with
  | false =>
      simp only [CoreRules.principalCore, CoreRules.generateCore, supported,
        Bool.false_eq_true, ↓reduceIte, normalise, List.not_mem_nil] at member
  | true =>
      apply generated_width_atoms (CoreRules.decode expression) clause
      simpa only [CoreRules.principalCore, CoreRules.generateCore, supported, ↓reduceIte, principal]
        using member

end Yulang.PresenceGeneratedWidth
