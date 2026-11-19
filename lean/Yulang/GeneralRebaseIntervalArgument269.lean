import Yulang.GeneralRebaseSlotInequalities269

namespace Yulang.GeneralRebaseIntervalArgument269
open GeneralNominalState (State Descriptor Models Fits)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalProjections (Observes)
open GeneralRebaseActualArguments269 (Member)
open GeneralRebaseSlotInequalities269 (Bound prove prove_sound)
open GeneralRebasePartialBool268 (Answer Reflect)
open CommonNominalFullCarrier

theorem observed_fits (state : State) (model : Assignment) (valid : Models state model)
 (parent : Fin state.base.slots) (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (i : Nat) (lo hi : Fin state.base.slots) (located : d.arguments[i]? = some (.type (lo,hi)))
 (actual : Ty)
 (seen : Observes model (.argument (.source (state.base.source parent)) d.declaration.name i) (.inl actual)) :
 Fits state.base model (.type (lo,hi)) (.inl actual) := by
 obtain ⟨known,other,good⟩ := GeneralNominalProjections.parameter_binding_valid
   state model valid parent d recorded i 0 (.type (lo,hi)) located
 have same := GeneralNominalProjections.observation_unique model _ _ _ seen other
 cases known with
 | inr => cases good
 | inl value =>
   exact ⟨subtype_trans good.1 same.2,subtype_trans same.1 good.2⟩

theorem interval_tight (state : State) (parent child : Fin state.base.slots)
 (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (i : Nat) (lo hi : Fin state.base.slots) (located : d.arguments[i]? = some (.type (lo,hi)))
 (lower : Bound state child lo) (upper : Bound state hi child) :
 Member state parent child d i := by
 intro model valid
 obtain ⟨value,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid
   state model valid parent d recorded i 0 (.type (lo,hi)) located
 cases value with
 | inr => cases fits
 | inl actual =>
   exact ⟨actual,seen,subtype_trans fits.2 (upper model valid),subtype_trans (lower model valid) fits.1⟩

theorem interval_necessary (state : State) (parent child : Fin state.base.slots)
 (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (i : Nat) (lo hi : Fin state.base.slots) (located : d.arguments[i]? = some (.type (lo,hi)))
 (given : Member state parent child d i) : Bound state lo child ∧ Bound state child hi := by
 constructor <;> intro model valid
 · obtain ⟨actual,seen,eq⟩ := given model valid
   exact subtype_trans (observed_fits state model valid parent d recorded i lo hi located actual seen).1 eq.1
 · obtain ⟨actual,seen,eq⟩ := given model valid
   exact subtype_trans eq.2 (observed_fits state model valid parent d recorded i lo hi located actual seen).2

/-- Positive finite certificates use the reverse inequalities that make
every fitted argument equal to the target. A certified failure of either
forward necessary inequality proves the negative. Failure of finite
positive proof search itself is only unknown. -/
def probe (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (child lo hi : Fin state.base.slots) : Answer :=
 if prove state child lo && prove state hi child then some true
 else if bound lo child == some false || bound child hi == some false then some false
 else none

theorem probe_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b))
 (parent child : Fin state.base.slots) (d : Descriptor state.base.slots)
 (recorded : state.nominals parent = some d) (i : Nat) (lo hi : Fin state.base.slots)
 (located : d.arguments[i]? = some (.type (lo,hi))) :
 Reflect (Member state parent child d i) (probe state bound child lo hi) := by
 unfold probe
 split
 · rename_i known
   have signs := (Bool.and_eq_true ..).mp known
   exact interval_tight state parent child d recorded i lo hi located
     (prove_sound state _ _ signs.1) (prove_sound state _ _ signs.2)
 · split
   · rename_i no
     intro supported
     have bounds := interval_necessary state parent child d recorded i lo hi located supported
     rcases (Bool.or_eq_true ..).mp no with lower | upper
     · have contradicted := cert lo child
       rw [beq_iff_eq.mp lower] at contradicted
       exact contradicted bounds.1
     · have contradicted := cert child hi
       rw [beq_iff_eq.mp upper] at contradicted
       exact contradicted bounds.2
   · trivial

end Yulang.GeneralRebaseIntervalArgument269
