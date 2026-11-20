import Yulang.GeneralMixedControlTrace306
import Yulang.GeneralRebaseSignedRefresh297
import Yulang.GeneralRebaseSignedDepth297

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralMixedPreInstallSigns306
open GeneralDictionaryOutputDepth252 (roles initial registry root plan model frame)
open GeneralDictionaryOutputDepthInstall252 (smallModel)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDepthPathKeep285 (Located of_frame)
open GeneralRebaseRetarget275 (Observed)
open GeneralRebaseSignedRefresh297 (moved refinement interp preserves_test)
open GeneralRebaseSignedModels297 (Sign Test Conditions)
open GeneralRebaseSignedDepth297 (positive negative nested)
open GeneralMixedControlTrace306 (RawTrace)
open GeneralMixedControlBisim306 (Observe)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralRebasePriorWitness297 (Prior values vote)
open GeneralRebaseFiniteWitnessTable297 (Covers)
open GeneralRebaseSourceQuestions297 (holds questions question_exact)
variable {s : State roles}

structure Tracked (s : State roles) (p : Plan roles) : Prop where
  location : Located s p
  observed : Observed p
  signs : ∀ side m, Test s p side m ↔ Test initial plan side m

theorem start : Tracked initial plan :=
  ⟨of_frame frame,GeneralRebaseDepthCommit285.seen,fun _ _ => Iff.rfl⟩

theorem follow {p : Plan roles} (was : Tracked s p) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) : Tracked (refresh s ctx) (moved cert was.location.context_eq) := by
  let loc := was.location
  let ref := refinement cert loc.context_eq
  let intp := interp cert loc.context_eq
  refine ⟨⟨loc.registry_eq,rfl,loc.declaration_eq,loc.raw_recorded,loc.center_recorded,?_⟩,
    GeneralRebaseRetarget275.observed p ref intp was.observed,
    fun side m => (preserves_test cert loc.context_eq was.observed side m).trans (was.signs side m)⟩
  exact GeneralDictionaryRefinedLocations.arguments p.packet.context ctx ref
    (GeneralNominalVersionedCandidates231.inputs root) p.packet.bounds loc.located

theorem after_every (path : RawTrace initial itinerary s) : ∃ p, Tracked s p := by
  have progress {a b : State roles} {xs} (given : RawTrace a xs b) :
      (∃ p, Tracked a p) → ∃ p, Tracked b p := by
    induction given with
    | done => exact id
    | advance obs _ ih =>
      intro existsPlan
      obtain ⟨p,known⟩ := existsPlan
      apply ih
      cases obs with
      | refresh ctx cert _ _ _ => exact ⟨_,follow known ctx cert⟩
  exact progress path ⟨plan,start⟩

theorem explicit {p : Plan roles} (tracked : Tracked s p) :
    Test s p .pass model ∧ Test s p .reject smallModel :=
  ⟨(tracked.signs .pass _).mpr positive,(tracked.signs .reject _).mpr negative⟩

def twoRows {p : Plan roles} (tracked : Tracked s p) : List (GeneralRebasePriorWitness297.Prior s) :=
  [⟨model,(explicit tracked).1.1⟩,⟨smallModel,(explicit tracked).2.1⟩]

def check (_ : Plan roles) (row : GeneralRebasePriorWitness297.Prior s) : Bool := nested row.val

theorem checked_rows {p : Plan roles} (tracked : Tracked s p)
    (row : GeneralRebasePriorWitness297.Prior s) (listed : row ∈ twoRows tracked) :
    check p row = true ↔ Conditions s p row.val := by
  simp only [twoRows,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl
  · exact ⟨fun _ => (explicit tracked).1.2,fun _ => rfl⟩
  · constructor
    · intro impossible
      cases impossible
    · intro yes
      exact ((explicit tracked).2.2 yes).elim

theorem covers {p : Plan roles} (tracked : Tracked s p) :
    Covers (holds s) (questions [p]) (values (twoRows tracked)) := by
  rintro ⟨q,side⟩ request _
  have equal : q = p := List.mem_singleton.mp ((question_exact [p] q side).mp request)
  subst q
  cases side
  · exact ⟨model,List.mem_map_of_mem (List.mem_cons_self ..),(explicit tracked).1⟩
  · exact ⟨smallModel,List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)),(explicit tracked).2⟩

theorem signed_compiler_exact {p : Plan roles} (tracked : Tracked s p) (side : Sign) :
    vote (twoRows tracked) check p side = true ↔ ∃ m, Test s p side m :=
  GeneralRebasePriorWitness297.vote_exact (covers tracked) check p (List.mem_singleton_self _) (checked_rows tracked) side

theorem both_bits {p : Plan roles} (tracked : Tracked s p) :
    vote (twoRows tracked) check p .pass = true ∧ vote (twoRows tracked) check p .reject = true :=
  ⟨rfl,rfl⟩

/-- The signed finite probe for this retained actual plan can be constructed
after any prior refresh-only path, even when its caches or slot indices vary. -/
theorem exact_on_any_prior_path (path : RawTrace initial itinerary s) :
    ∃ p, ∃ tracked : Tracked s p, ∀ side, vote (twoRows tracked) check p side = true ↔ ∃ m, Test s p side m := by
  obtain ⟨p,tracked⟩ := after_every path
  exact ⟨p,tracked,signed_compiler_exact tracked⟩

end Yulang.GeneralMixedPreInstallSigns306
