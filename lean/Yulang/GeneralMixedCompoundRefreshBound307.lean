import Yulang.GeneralMixedCompoundTail307
import Yulang.GeneralNominalKnownBit304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundRefreshBound307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSnapshot307 (snap refineRaw)
open GeneralMixedCompoundUpperSupport307 (headless unknown_cases known_0 known_1 known_2 known_lo known_hi)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalState (sources Known)
open GeneralNominalKnownBit304 (knownBit known_exact)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates (Context)

abbrev k (s : State roles) (n : Nat) := Known s.core.erased.current.context.state n
abbrev pool (s : State roles) := sources s.core.erased.current.context.state

inductive Run : Nat → State roles → Prop
  | zero : Run 0 point
  | more {n s} (prior : Run n s) (ctx : Context) (cert : Refresh s ctx)
      (source : Nat) : source ∈ pool s → ¬ k s source → Known ctx.state source →
      Run (n+1) (refresh s ctx)

theorem actual (p : Run n s) : B4Target.Steps (Step registry root) point s := by
  induction p with
  | zero => exact .refl
  | more p ctx cert id present unknown known ih =>
    exact .tail ih ⟨root,.root,.refresh root ctx cert id present unknown known⟩

theorem models (p : Run n s) (m : Assignment) : Models s m ↔ Models upperState m := by
  induction p with
  | zero => exact (GeneralDictionaryCompoundRefresh239.models_iff m).symm.trans ((GeneralMixedCompoundUpperRefresh307.models_iff m).symm)
  | more _ ctx cert id present unknown known ih =>
    exact (refresh_models cert).trans ih

theorem support (p : Run n s) : pool s ⊆ sources snap := by
  induction p with
  | zero => intro i found
            exact GeneralNominalRefinements.sources refineRaw _
              (GeneralNominalRefinements.sources GeneralDictionaryCompoundSnapshot239.refines _ found)
  | more _ ctx cert _ _ _ _ ih =>
    intro i found
    exact ih (cert.support i found)

theorem root_known (p : Run n s) : ∀ i, k point i → k s i := by
  induction p with
  | zero => exact fun _ h => h
  | more _ ctx cert _ _ _ _ ih => exact fun i h => cert.refines.known i (ih i h)

theorem supported_gain (p : Run n s) (ctx : Context) (cert : Refresh s ctx)
    (n : Nat) (present : n ∈ pool s) (old : ¬ k s n) (new : Known ctx.state n) :
    n = lo ∨ n = hi ∨ n = upper := by
  by_cases inUpper : Known snap n
  · rcases GeneralMixedCompoundAnyRefresh307.known_origin n inUpper with h|prev
    · exact Or.inr (Or.inr h)
    · obtain ⟨i,idEq,flag⟩ := prev
      have casesSlot : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide +kernel
      rcases casesSlot i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact False.elim (old (root_known p n ⟨(0 : Fin 5),idEq,Or.inr ⟨_,rfl⟩⟩))
      · exact False.elim (old (root_known p n ⟨(1 : Fin 5),idEq,Or.inr ⟨_,rfl⟩⟩))
      · exact False.elim (old (root_known p n ⟨(2 : Fin 5),idEq,Or.inl (by decide +kernel)⟩))
      · rcases flag with invalid|⟨_,invalid⟩
        · exact False.elim (invalid rfl)
        · cases invalid
      · rcases flag with invalid|⟨_,invalid⟩
        · exact False.elim (invalid rfl)
        · cases invalid
      · exact Or.inl idEq.symm
      · exact Or.inr (Or.inl idEq.symm)
  · obtain ⟨m,valid,nohead⟩ := headless
    have ready := (refresh_models cert).mpr ((models p _).mpr valid)
    obtain ⟨test,obs,headed⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head new
    have fact := GeneralCanonicalObservations.recorded_sound ctx.state m ready.1.1
      (GeneralNominalSupport.head_recorded headed)
    exact False.elim (nohead n (support p present) inUpper test
      (GeneralDictionaryGroundCopy218Refresh.head_holds headed fact))

def score (s : State roles) : Nat :=
  (knownBit s.core.erased.current.context.state lo).toNat +
  (knownBit s.core.erased.current.context.state hi).toNat +
  (knownBit s.core.erased.current.context.state upper).toNat

theorem bit_le (ctx : Context) (cert : Refresh s ctx) (i : Nat) :
    (knownBit s.core.erased.current.context.state i).toNat ≤ (knownBit ctx.state i).toNat := by
  cases h : knownBit s.core.erased.current.context.state i
  · exact Nat.zero_le _
  · rw [(known_exact ..).mpr (cert.refines.known i ((known_exact ..).mp h))] <;> decide

theorem bit_lt {s : State roles} (ctx : Context) (i : Nat)
    (old : ¬ k s i) (new : Known ctx.state i) :
    (knownBit s.core.erased.current.context.state i).toNat < (knownBit ctx.state i).toNat := by
  rw [(known_exact ..).mpr new]
  cases h : knownBit s.core.erased.current.context.state i
  · decide
  · exact False.elim (old ((known_exact ..).mp h))

theorem score_lt (p : Run n s) (ctx : Context) (cert : Refresh s ctx) (i : Nat)
    (present : i ∈ pool s) (old : ¬ k s i) (new : Known ctx.state i) :
    score s < score (refresh s ctx) := by
  have a := bit_le ctx cert lo
  have b := bit_le ctx cert hi
  have c := bit_le ctx cert upper
  have later := bit_lt ctx i old new
  unfold score
  change _ < (knownBit ctx.state lo).toNat + (knownBit ctx.state hi).toNat + (knownBit ctx.state upper).toNat
  rcases supported_gain p ctx cert i present old new with rfl|rfl|rfl <;> omega

theorem score_le (s : State roles) : score s ≤ 3 := by
  have atMost (i : Nat) : (knownBit s.core.erased.current.context.state i).toNat ≤ 1 := by
    cases knownBit s.core.erased.current.context.state i <;> decide
  unfold score
  have a := atMost lo; have b := atMost hi; have c := atMost upper
  omega

theorem length_le_score (p : Run n s) : n ≤ score s := by
  induction p with
  | zero => exact Nat.zero_le _
  | more p ctx cert i present old new ih =>
    exact Nat.le_trans (Nat.succ_le_succ ih) (score_lt p ctx cert i present old new)

theorem bound (p : Run n s) : n ≤ 3 := Nat.le_trans (length_le_score p) (score_le s)

end Yulang.GeneralMixedCompoundRefreshBound307
