import Yulang.CommonEffectTypeNormalisation
import Yulang.CommonRecord

/-! Recursive decomposition of known finite constructor comparisons, beneath
all original effect binders. Unknown/captured comparisons remain ordinary
finite type atoms. This pass does not certify elimination of all universals. -/
namespace Yulang.CommonEffectConstructorNormalisation
open Core.PresenceGeneration (TyTerm)
open CommonEffectRequestGeneration (Computation RowExpr)
open CommonEffectFormula (Formula)

variable {scopes : Nat}

def weight : TyTerm α → Nat
  | .var _ | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => 1
  | .required _ body | .variant _ body => 1 + weight body
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => 1 + weight first + weight last
  | .arrow arg _ result _ => 1 + weight arg + weight result

theorem weight_positive (term : TyTerm α) : 0 < weight term := by
  cases term <;> simp only [weight] <;> omega

def atom (source target : TyTerm α) : Formula scopes α :=
  match source, target with
  | .bottom, _ => .core .top
  | _, .top => .core .top
  | .union first last, target => .and (atom first target) (atom last target)
  | source, .inter first last => .and (atom source first) (atom source last)
  | .pair a b, .pair c d => .and (atom a c) (atom b d)
  | .arrow arg incoming result outgoing, .arrow arg' incoming' result' outgoing' =>
      .and (atom arg' arg) (.and (.rowLe (RowExpr.fromPresence incoming') (RowExpr.fromPresence incoming))
        (.and (atom result result') (.rowLe (RowExpr.fromPresence outgoing) (RowExpr.fromPresence outgoing'))))
  | .variant label payload, .variant label' payload' =>
      if label = label' then atom payload payload' else .tyLe source target
  | .required label payload, .required label' payload' =>
      if label = label' then atom payload payload' else .tyLe source target
  | .record label payload _, .required label' payload' =>
      if label = label' then atom payload payload' else .tyLe source target
  | source, target => .tyLe source target
termination_by weight source + weight target
decreasing_by all_goals simp_wf; simp only [weight]; omega

theorem required_iff (label : Nat) (first last : Common.Ty) :
    Common.Subtype (Common.required label first) (Common.required label last) ↔ Common.Subtype first last :=
  Common.common_singleton_requirement_iff label first last Common.emptyRecord

theorem atom_exact (source target : TyTerm α) (assignment : α → Computation) :
    (atom (scopes := scopes) source target).Holds assignment ↔
      Common.Subtype (source.eval Common.model assignment) (target.eval Common.model assignment) := by
  fun_induction atom source target
  all_goals simp_all only [Formula.Holds, Formula.holds_tyLe, TyTerm.eval, Common.model,
    Core.PresenceGeneration.Formula.Holds, RowExpr.eval_fromPresence,
    CommonEffectTypeNormalisation.subtype_top, CommonEffectTypeNormalisation.bottom_subtype,
    CommonEffectTypeNormalisation.inter_upper_iff, CommonEffectUniversalArms.union_le_iff,
    required_iff, Common.common_singleton_requirement_iff]
  all_goals first
    | exact (Common.common_pair_iff _ _ _ _).symm
    | exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).symm
    | exact (Common.common_variant_iff _ _ _).symm

def core : Core.PresenceGeneration.Formula α → Formula scopes α
  | .top => .core .top
  | .bot => .core .bot
  | .tyLe source target => atom source target
  | .rowLe source target => .core (.rowLe source target)
  | .and first last => .and (core first) (core last)
  | .or first last => .or (core first) (core last)
  | .existsSlot body => .existsSlot (core body)

theorem core_exact (formula : Core.PresenceGeneration.Formula α) (assignment : α → Computation) :
    (core (scopes := scopes) formula).Holds assignment ↔ formula.Holds Common.model assignment := by
  induction formula <;> simp_all only [core, Formula.Holds,
    Core.PresenceGeneration.Formula.Holds, atom_exact]
  all_goals rfl

def normalise : Formula scopes α → Formula scopes α
  | .core body => core body
  | .rowLe source target => .rowLe source target
  | .and first last => .and (normalise first) (normalise last)
  | .or first last => .or (normalise first) (normalise last)
  | .existsSlot body => .existsSlot (normalise body)
  | .existsTypes count body => .existsTypes count (normalise body)
  | .forallTypes count body => .forallTypes count (normalise body)

theorem normalise_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (normalise formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula <;> simp_all only [normalise, Formula.Holds, core_exact]

end Yulang.CommonEffectConstructorNormalisation
