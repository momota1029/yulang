import Yulang.CommonEffectGrammarBoundary
import Yulang.CommonEffectUniversalArms

/-! Demand-order normalization for arbitrary finite effect formulas. This
reduces some signature shapes outside the old generated grammar, preserving
all ambient assignments and both kinds of local type quantifiers. It does not
eliminate universal types or certify the old grammar for every declaration. -/
namespace Yulang.CommonEffectTypeNormalisation
open Core.PresenceGeneration (TyTerm CompTerm RowTerm extend)
open CommonEffectRequestGeneration (Computation)
open CommonEffectFormula

variable {scopes : Nat}

theorem subtype_top (source : Common.Ty) : Common.Subtype source .top := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation accepted
  cases rank <;> cases observation <;>
    simp_all [Common.observeTy, CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt,
      CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem bottom_subtype (target : Common.Ty) : Common.Subtype .bottom target := by
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank environment observation _
  exact CommonFinite.probeAt_bottom rank observation

theorem inter_upper_iff (source first last : Common.Ty) :
    Common.Subtype source (.inter first last) ↔ Common.Subtype source first ∧ Common.Subtype source last := by
  constructor
  · intro below
    exact ⟨fun depth => ((CommonFinite.producerLe_inter_iff _ _ _).mp (below depth)).1,
      fun depth => ((CommonFinite.producerLe_inter_iff _ _ _).mp (below depth)).2⟩
  · rintro ⟨firstLe, lastLe⟩ depth
    exact (CommonFinite.producerLe_inter_iff _ _ _).mpr ⟨firstLe depth, lastLe depth⟩

def normaliseUpper (source : TyTerm α) : TyTerm α → Formula scopes α
  | .top => .core .top
  | .inter first last => .and (normaliseUpper source first) (normaliseUpper source last)
  | target => .core (.tyLe source target)

theorem normaliseUpper_exact (source target : TyTerm α) (assignment : α → Computation) :
    (normaliseUpper (scopes := scopes) source target).Holds assignment ↔
      Common.Subtype (source.eval Common.model assignment) (target.eval Common.model assignment) := by
  induction target with
  | top => exact ⟨fun _ => subtype_top _, fun _ => trivial⟩
  | inter first last firstIH lastIH =>
    change (_ ∧ _) ↔ Common.Subtype _ (.inter _ _)
    exact (and_congr firstIH lastIH).trans
      (inter_upper_iff (source.eval Common.model assignment)
        (first.eval Common.model assignment) (last.eval Common.model assignment)).symm
  | _ => rfl

def normaliseAtom : TyTerm α → TyTerm α → Formula scopes α
  | .bottom, _ => .core .top
  | .union first last, target => .and (normaliseAtom first target) (normaliseAtom last target)
  | source, target => normaliseUpper source target

theorem normaliseAtom_exact (source target : TyTerm α) (assignment : α → Computation) :
    (normaliseAtom (scopes := scopes) source target).Holds assignment ↔
      Common.Subtype (source.eval Common.model assignment) (target.eval Common.model assignment) := by
  induction source with
  | bottom => exact ⟨fun _ => bottom_subtype _, fun _ => trivial⟩
  | union first last firstIH lastIH =>
    change (_ ∧ _) ↔ Common.Subtype (.union _ _) _
    exact (and_congr firstIH lastIH).trans
      (CommonEffectUniversalArms.union_le_iff (first.eval Common.model assignment)
        (last.eval Common.model assignment) (target.eval Common.model assignment)).symm
  | _ => exact normaliseUpper_exact _ _ assignment

def normaliseCore : Core.PresenceGeneration.Formula α → Formula scopes α
  | .top => .core .top
  | .bot => .core .bot
  | .and first last => .and (normaliseCore first) (normaliseCore last)
  | .or first last => .or (normaliseCore first) (normaliseCore last)
  | .tyLe first last => normaliseAtom first last
  | .rowLe first last => .core (.rowLe first last)
  | .existsSlot body => .existsSlot (normaliseCore body)

theorem normaliseCore_exact (formula : Core.PresenceGeneration.Formula α) (assignment : α → Computation) :
    (normaliseCore (scopes := scopes) formula).Holds assignment ↔ formula.Holds Common.model assignment := by
  induction formula <;> simp_all [normaliseCore, Formula.Holds,
    Core.PresenceGeneration.Formula.Holds, normaliseAtom_exact]
  all_goals rfl

def normalise : Formula scopes α → Formula scopes α
  | .core body => normaliseCore body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (normalise first) (normalise last)
  | .or first last => .or (normalise first) (normalise last)
  | .existsSlot body => .existsSlot (normalise body)
  | .existsTypes count body => .existsTypes count (normalise body)
  | .forallTypes count body => .forallTypes count (normalise body)

/-- Every finite formula and assignment, including arbitrary captured schemes
and all nested universal/existential local type binders. -/
theorem normalise_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (normalise formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula <;> simp_all only [normalise, Formula.Holds, normaliseCore_exact]
/-- The old child grammar lifted only for verifying preprocessing results. -/
def OldChildGrammar : Formula scopes α → Prop
  | .core body => PresenceGeneratedChildGrammar.GoodFormula body
  | .rowLe _ _ => True
  | .and first last | .or first last => OldChildGrammar first ∧ OldChildGrammar last
  | .existsSlot body => OldChildGrammar body
  | .existsTypes _ body | .forallTypes _ body => OldChildGrammar body

/-- The earlier well-kinded top-input counterexample is repaired by an exact
normalization, rather than by excluding that declaration or payload. -/
theorem top_request_normalises_into_old_grammar :
    OldChildGrammar (normalise (CommonEffectFormula.ofConstraint
      (CommonEffectRequestGeneration.generateRequest (scopes := scopes) []
        (CommonEffectGrammarBoundary.acceptsAny : CommonEffectRequestGeneration.Declaration Unit)
        (.lit .unit) (CompTerm.var ())))) := by
  simp [OldChildGrammar, normalise, normaliseCore, normaliseAtom, normaliseUpper,
    ofConstraint, CommonEffectRequestGeneration.generateRequest,
    CommonEffectRequestGeneration.requestBody, CommonEffectGrammarBoundary.acceptsAny,
    Core.PresenceGeneration.generate, Core.PresenceGeneration.Formula.compLe,
    PresenceGeneratedChildGrammar.GoodFormula, PresenceGeneratedChildGrammar.lower,
    PresenceGeneratedChildGrammar.upper, TyTerm.rename, CompTerm.rename, CompTerm.var, CompTerm.pure]
end Yulang.CommonEffectTypeNormalisation
