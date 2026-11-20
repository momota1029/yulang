import Yulang.GeneralRebaseSourceWitnessProgram297

namespace Yulang.GeneralRebaseWitnessContracts297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseSourceQuestions297 (entries of_focus)
open GeneralRebaseHeadProbe267 (Honest atFocus)
open GeneralRebaseFiniteWitnessTable297 (Covers hit hit_exact)
open GeneralRebaseSourceWitnessProgram297
open GeneralRebaseSignedModels297 (Sign)

variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
  {checked : (Boundary roles).Checked r} {xs : List Assignment} {c : Checks roles}

theorem install_coverage
    (covered : Covers (Holds s) (questions r s root checked) xs) :
    Covers (GeneralRebaseSourceQuestions297.holds s)
      (GeneralRebaseSourceQuestions297.questions (entries r s root checked)) xs := by
  rintro ⟨p,sign⟩ present witness
  exact covered (.install p sign)
    (install_listed r s root checked p ((GeneralRebaseSourceQuestions297.question_exact _ p sign).mp present) sign) witness

theorem merge_coverage
    (covered : Covers (Holds s) (questions r s root checked) xs) :
    Covers (GeneralRebaseMergeQuestions297.counter s) (registeredPairs s) xs :=
  fun pair listed yes => covered (.mergeFailure pair) (merge_listed r s root checked pair listed) yes

theorem head_exact
    (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c) (p : Plan roles)
    (listed : p ∈ entries r s root checked) :
    hit xs c.head p = true ↔ GeneralRebaseCandidatePrepared267.headCondition p := by
  let forHead : Covers headTest (entries r s root checked) xs :=
    fun q mem h => covered (.head q) (head_listed r s root checked q mem) h
  exact hit_exact headTest _ xs forHead c.head p listed (cert.1 p listed)

theorem honest
    (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (f : Occurrence roles) (generated : Generated s.core.erased.current root f) :
    Honest ((callbacks xs c).head f) (atFocus (Encoded r) s root f (declChecked checked)) := by
  have exactHead (p : Plan roles) (listed : p ∈ atFocus (Encoded r) s root f (declChecked checked)) :=
    head_exact covered cert p (of_focus r s root f checked generated p listed)
  constructor
  · intro p listed yes
    exact (exactHead p listed).mp (Option.some.inj yes)
  · intro p listed no yes
    have bit := (exactHead p listed).mpr yes
    have different := Option.some.inj no
    rw [bit] at different
    cases different

theorem head_total (f : Occurrence roles) :
    GeneralRebaseCompleteHeadProbe267.Covered ((callbacks xs c).head f)
      (atFocus (Encoded r) s root f (declChecked checked)) :=
  by intro p _ bad; cases bad

theorem merge_exact
    (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (first : Site roles) (one : first ∈ s.core.sites) (last : Site roles) (two : last ∈ s.core.sites) :
    (callbacks xs c).mergeInputs first last = true ↔ SameInputs (Models s) first last := by
  have pair := (pairs_exact s first last).mpr ⟨one,two⟩
  exact GeneralRebaseMergeQuestions297.equal_exact s _ xs (merge_coverage covered)
    (mergeBit c) (first,last) pair (mergeBit_exact cert (first,last) pair)

theorem all_observer_contracts
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (covered : Covers (Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (entries r s root checked) c)
    (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded r) s.core.erased.current.context)
    (diagnostics : ∀ f, ∀ p ∈ GeneralRebaseSourceObserver267.installAt r s root f checked (callbacks xs c),
       GeneralRebaseSourceSelect267.Guard r s f p.packet.declaration.id) :
    GeneralRebaseObserverSound267.Sound r s root checked (callbacks xs c) ∧
      GeneralRebaseObserverCoverage267.Covers r s root checked (callbacks xs c) := by
  apply GeneralRebaseSignedObserver297.contracts reach (install_coverage covered) cert.2.1
  exact ⟨metadata,honest covered cert,fun f _ => head_total (checked := checked) f,diagnostics,merge_exact covered cert⟩

end Yulang.GeneralRebaseWitnessContracts297
