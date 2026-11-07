import Yulang.CommonEffectRowQuantifiers
import Yulang.CommonEffectTypeNormalisation
import Yulang.CommonDefault
import Yulang.CommonPresence

/-! Syntactic variance for the whole finite effect formula. Bound computation
witnesses are kept fixed, so coupled value/row constraints are not split.
Uniform-polarity local universals can be eliminated by an extremal type;
mixed-polarity locals are deliberately not certified by this pass. -/
namespace Yulang.CommonEffectPolarity
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula

variable {scopes : Nat}

/-- none freezes the value in both directions; rows are always kept literal. -/
abbrev Orientation (α : Type) := α → Option Bool

def Directed (positive : Bool) (first last : Common.Ty) : Prop :=
  if positive then Common.Subtype first last else Common.Subtype last first

def Ordered (orientation : Orientation α) (first last : α → Computation) : Prop :=
  (∀ name, (first name).2 = (last name).2) ∧
  ∀ name, match orientation name with
    | none => Common.Equivalent (first name).1 (last name).1
    | some positive => Directed positive (first name).1 (last name).1

def goodType (orientation : Orientation α) (positive : Bool) : TyTerm α → Bool
  | .var name => match orientation name with
      | none => true
      | some direction => direction == positive
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => true
  | .union first last | .inter first last | .pair first last |
      .recordDefault _ first last | .record _ first last =>
      goodType orientation positive first && goodType orientation positive last
  | .required _ body | .variant _ body => goodType orientation positive body
  | .arrow input _ output _ =>
      goodType orientation (!positive) input && goodType orientation positive output

theorem ordered_variable (orientation : Orientation α) (first last : α → Computation)
    (ordered : Ordered orientation first last) (positive : Bool) (name : α)
    (good : goodType orientation positive (.var name) = true) :
    Directed positive (first name).1 (last name).1 := by
  have related := ordered.2 name
  cases found : orientation name with
  | none =>
    rw [found] at related
    cases positive with
    | false => exact related.2
    | true => exact related.1
  | some direction =>
    have same : direction = positive := by simpa [goodType, found] using good
    simpa [found, same] using related

theorem type_ordered (term : TyTerm α) (orientation : Orientation α) (first last : α → Computation)
    (ordered : Ordered orientation first last) (positive : Bool)
    (good : goodType orientation positive term = true) :
    Directed positive (term.eval Common.model first) (term.eval Common.model last) := by
  induction term generalizing positive with
  | var name => exact ordered_variable orientation first last ordered positive name good
  | base | bottom | top | emptyRecord | exactEmpty =>
    cases positive <;> exact Common.subtype_refl _
  | union a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    cases positive <;> exact Common.common_union_mono (iha _ both.1) (ihb _ both.2)
  | inter a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    cases positive <;> exact Common.common_inter_mono (iha _ both.1) (ihb _ both.2)
  | pair a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    cases positive <;> exact (Common.common_pair_iff _ _ _ _).mpr ⟨iha _ both.1, ihb _ both.2⟩
  | required label body ih =>
    cases positive <;> exact Common.common_record_mono label (ih _ good) (Common.subtype_refl _)
  | variant label body ih =>
    cases positive <;> exact (Common.common_variant_iff label _ _).mpr (ih _ good)
  | record label payload rest ihp ihr =>
    have both := Bool.and_eq_true_iff.mp good
    cases positive <;> exact Common.common_record_mono label (ihp _ both.1) (ihr _ both.2)
  | recordDefault label source fallback ihs ihf =>
    have both := Bool.and_eq_true_iff.mp good
    cases positive <;> exact Common.common_default_mono label (ihs _ both.1) (ihf _ both.2)
  | arrow input incoming output outgoing ihi iho =>
    have both := Bool.and_eq_true_iff.mp good
    have sameIncoming := CommonEffectRowQuantifiers.rowTerm_congr incoming first last ordered.1
    have sameOutgoing := CommonEffectRowQuantifiers.rowTerm_congr outgoing first last ordered.1
    cases positive <;>
      apply (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr <;>
      refine ⟨ihi _ both.1, ?_, iho _ both.2, ?_⟩ <;>
      first | simpa only [sameIncoming] using Common.rowLe_refl (incoming.eval Common.model last)
            | simpa only [sameOutgoing] using Common.rowLe_refl (outgoing.eval Common.model last)

def lift (orientation : Orientation α) : Orientation (Option α)
  | none => none
  | some name => orientation name

def localOrientation (orientation : Orientation α) : Orientation (α ⊕ Fin count)
  | .inl name => orientation name
  | .inr _ => none

theorem ordered_extend (orientation : Orientation α) (first last : α → Computation)
    (ordered : Ordered orientation first last) (value : Computation) :
    Ordered (lift orientation) (extend first value) (extend last value) := by
  refine ⟨CommonEffectRowQuantifiers.extend_rows first last value ordered.1, ?_⟩
  intro name
  cases name with
  | none => exact Common.equivalent_refl _
  | some name => exact ordered.2 name

theorem ordered_local (orientation : Orientation α) (first last : α → Computation)
    (ordered : Ordered orientation first last) (types : Fin count → Common.Ty) :
    Ordered (localOrientation orientation) (localEnv first types) (localEnv last types) := by
  refine ⟨CommonEffectRowQuantifiers.local_rows first last types ordered.1, ?_⟩
  intro name
  cases name with
  | inl name => exact ordered.2 name
  | inr name => exact Common.equivalent_refl _

def goodCore (orientation : Orientation α) : Core.PresenceGeneration.Formula α → Bool
  | .top | .bot | .rowLe _ _ => true
  | .tyLe first last => goodType orientation false first && goodType orientation true last
  | .and first last | .or first last => goodCore orientation first && goodCore orientation last
  | .existsSlot body => goodCore (lift orientation) body

theorem core_ordered (formula : Core.PresenceGeneration.Formula α) (orientation : Orientation α)
    (first last : α → Computation) (ordered : Ordered orientation first last)
    (good : goodCore orientation formula = true) :
    formula.Holds Common.model first → formula.Holds Common.model last := by
  induction formula with
  | top | bot => exact id
  | tyLe a b =>
    have both := Bool.and_eq_true_iff.mp good
    intro below
    exact Common.subtype_trans (type_ordered a orientation first last ordered false both.1)
      (Common.subtype_trans below (type_ordered b orientation first last ordered true both.2))
  | rowLe a b =>
    simp only [Core.PresenceGeneration.Formula.Holds,
      CommonEffectRowQuantifiers.rowTerm_congr a first last ordered.1,
      CommonEffectRowQuantifiers.rowTerm_congr b first last ordered.1]
    exact id
  | and a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact fun held => ⟨iha _ _ _ ordered both.1 held.1, ihb _ _ _ ordered both.2 held.2⟩
  | or a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact fun held => held.elim (fun ha => Or.inl (iha _ _ _ ordered both.1 ha))
      (fun hb => Or.inr (ihb _ _ _ ordered both.2 hb))
  | existsSlot body ih =>
    rintro ⟨value, held⟩
    exact ⟨value, ih _ _ _ (ordered_extend orientation first last ordered value) good held⟩

def goodFormula (orientation : Orientation α) : Formula scopes α → Bool
  | .core body => goodCore orientation body
  | .rowLe _ _ => true
  | .and first last | .or first last => goodFormula orientation first && goodFormula orientation last
  | .existsSlot body => goodFormula (lift orientation) body
  | .existsTypes _ body | .forallTypes _ body => goodFormula (localOrientation orientation) body

theorem formula_ordered (formula : Formula scopes α) (orientation : Orientation α)
    (first last : α → Computation) (ordered : Ordered orientation first last)
    (good : goodFormula orientation formula = true) :
    formula.Holds first → formula.Holds last := by
  induction formula with
  | core body => exact core_ordered body orientation first last ordered good
  | rowLe a b =>
    simp only [Formula.Holds, CommonEffectRowQuantifiers.rowExpr_congr a first last ordered.1,
      CommonEffectRowQuantifiers.rowExpr_congr b first last ordered.1]
    exact id
  | and a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact fun held => ⟨iha _ _ _ ordered both.1 held.1, ihb _ _ _ ordered both.2 held.2⟩
  | or a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp good
    exact fun held => held.elim (fun ha => Or.inl (iha _ _ _ ordered both.1 ha))
      (fun hb => Or.inr (ihb _ _ _ ordered both.2 hb))
  | existsSlot body ih =>
    rintro ⟨value, held⟩
    exact ⟨value, ih _ _ _ (ordered_extend orientation first last ordered value) good held⟩
  | existsTypes count body ih =>
    rintro ⟨types, held⟩
    exact ⟨types, ih _ _ _ (ordered_local orientation first last ordered types) good held⟩
  | forallTypes count body ih =>
    intro held types
    exact ih _ _ _ (ordered_local orientation first last ordered types) good (held types)

def localsOrientation (directions : Fin count → Bool) : Orientation (α ⊕ Fin count)
  | .inl _ => none
  | .inr index => some (directions index)

def extremalTypes (directions : Fin count → Bool) (index : Fin count) : Common.Ty :=
  if directions index then .bottom else .top

def extremalSubstitution (directions : Fin count → Bool) : α ⊕ Fin count → CompTerm α
  | .inl name => CompTerm.var name
  | .inr index => CompTerm.pure (if directions index then .bottom else .top)

theorem extremal_ordered (directions : Fin count → Bool) (assignment : α → Computation)
    (types : Fin count → Common.Ty) :
    Ordered (localsOrientation directions) (localEnv assignment (extremalTypes directions)) (localEnv assignment types) := by
  refine ⟨?_, ?_⟩
  · intro name
    cases name <;> rfl
  · intro name
    cases name with
    | inl name => exact Common.equivalent_refl _
    | inr index =>
      change Directed (directions index) (extremalTypes directions index) (types index)
      cases found : directions index <;> simp only [Directed, extremalTypes, found, Bool.false_eq_true, ↓reduceIte]
      · exact CommonEffectTypeNormalisation.subtype_top _
      · exact CommonEffectTypeNormalisation.bottom_subtype _

theorem extremalSubstitution_eval (directions : Fin count → Bool) (assignment : α → Computation) :
    (fun name => (extremalSubstitution directions name).eval Common.model assignment) =
      localEnv assignment (extremalTypes directions) := by
  funext name
  cases name with
  | inl name => rfl
  | inr index =>
    cases found : directions index <;>
      simp [extremalSubstitution, extremalTypes, localEnv, found, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
    all_goals rfl

/-- Syntactic certificate, arbitrary captured types and independent rows. The
eliminated formula contains no check on its future instantiation parameters. -/
theorem forall_extremal_exact (formula : Formula scopes (α ⊕ Fin count)) (directions : Fin count → Bool)
    (good : goodFormula (localsOrientation directions) formula = true) (assignment : α → Computation) :
    (formula.subst (extremalSubstitution directions)).Holds assignment ↔
      (Formula.forallTypes count formula).Holds assignment := by
  rw [Formula.holds_subst, extremalSubstitution_eval]
  constructor
  · intro held types
    exact formula_ordered formula _ _ _ (extremal_ordered directions assignment types) good held
  · intro held
    exact held (extremalTypes directions)
end Yulang.CommonEffectPolarity
