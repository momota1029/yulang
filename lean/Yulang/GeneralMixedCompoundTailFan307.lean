import Yulang.GeneralMixedCompoundTailPresentation307
import Yulang.GeneralNominalCatalogueExtension305
import Yulang.GeneralMixedReindexObserver305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralMixedCompoundTailFan307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSnapshot307 (context snap upper_known)
open GeneralMixedCompoundUpperRefresh307 (upperState cert)
open GeneralNominalCatalogueExtension305 (extend equivalent head_term)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRecursiveCandidates (Context)
open GeneralCanonicalObservations (Observation Recorded)
open GeneralNormalizedObservation (Head Shape)

def extra (tag : Nat) : Shape := .variant (tag+1)

theorem fresh (tag : Nat) (i : Fin snap.view.kinds) : snap.view.shapes i ≠ extra tag := by
  change Fin 2 at i
  have which : i = 0 ∨ i = 1 := by omega
  rcases which with rfl|rfl
  · intro eq; cases eq
  · intro eq
    have same := Shape.variant.inj eq
    change 0 = tag+1 at same
    omega

noncomputable def wide (tag : Nat) : Context :=
  ⟨extend snap (extra tag) (by trivial) (fresh tag),context.interpretation⟩

noncomputable def coordinates (tag : Nat) : GeneralNominalReportContext305.EquivalentContexts context (wide tag) :=
  equivalent context (extra tag) (by trivial) (fresh tag)

theorem recorded_term (i : Fin snap.base.slots)
    (term) (formed : (snap.view.heads i).term = some term) :
    Recorded snap (.normalized snap.base i term) := by
  cases h : snap.view.heads i with
  | scalar base =>
    rw [h] at formed
    cases Option.some.inj formed
    exact .scalar i base h
  | structural k children =>
    rw [h] at formed
    cases Option.some.inj formed
    exact .structural i k children h
  | deferred why =>
    have eq : why = .unresolved := by
      change GeneralMixedCompoundUpperBase307.viewHeads i = .deferred why at h
      unfold GeneralMixedCompoundUpperBase307.viewHeads at h
      split at h <;> (try split at h) <;> (try split at h) <;> cases h
      rfl
    subst why
    rw [h] at formed
    cases formed

theorem recorded_back (tag : Nat) (fact : Observation) (found : Recorded (wide tag).state fact) :
    Recorded snap fact := by
  cases found with
  | scalar i n h =>
    apply recorded_term
    have term := congrArg Head.term h
    change (GeneralNominalCatalogueExtension305.extendHead (extra tag) (snap.view.heads i)).term = some (.base n) at term
    rw [head_term] at term
    exact term
  | structural i k children h =>
    apply recorded_term
    have term := congrArg Head.term h
    change (GeneralNominalCatalogueExtension305.extendHead (extra tag) (snap.view.heads i)).term = _ at term
    rw [head_term] at term
    exact term
  | nominal i d found => exact Recorded.nominal (snapshot := snap) i d found

noncomputable def widthCert (tag : Nat) : Refresh refreshed (wide tag) := by
  let old := cert.refines
  refine ⟨⟨old.base,old.heads,old.nominals,old.ordinary,fun n known =>
    (coordinates tag).forward.known n (old.known n known),old.reserved,old.allocated,
    old.seed,old.constructors⟩,cert.interpretation,cert.support,cert.constraints,?_⟩
  intro observation found
  exact cert.cache observation (recorded_back tag observation found)

noncomputable def tail (tag : Nat) := refresh refreshed (wide tag)

theorem raw_halt (tag : Nat) :
    Step registry root refreshed (tail tag) ∧ ∀ after, ¬ Step registry root (tail tag) after := by
  have one := (coordinates tag).forward.known _ upper_known
  exact ⟨GeneralMixedCompoundTail307.seen (wide tag) (widthCert tag) one,
    GeneralMixedCompoundTail307.every_successor_halted (wide tag) (widthCert tag) one⟩

theorem injective : Function.Injective tail := by
  intro a b same
  have h := congrArg (fun s : State roles => List.ofFn s.core.erased.current.context.state.view.shapes) same
  change ([Shape.record [],Shape.variant 0,Shape.variant (a+1)] : List Shape) =
    [Shape.record [],Shape.variant 0,Shape.variant (b+1)] at h
  have eq := Shape.variant.inj (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
  omega

theorem infinitely_many_halts :
    ∃ f : Nat → State roles, Function.Injective f ∧
      ∀ n, Step registry root refreshed (f n) ∧ ∀ after, ¬ Step registry root (f n) after :=
  ⟨tail,injective,raw_halt⟩

end Yulang.GeneralMixedCompoundTailFan307
