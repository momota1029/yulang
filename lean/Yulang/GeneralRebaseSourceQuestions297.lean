import Yulang.GeneralRebaseFiniteWitnessTable297

namespace Yulang.GeneralRebaseSourceQuestions297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralRebaseHeadProbe267 (atFocus)
open GeneralRebaseSignedModels297 (Sign Test)
open GeneralRebaseFiniteWitnessTable297 (Covers samples hit hit_exact)

abbrev Question (roles : Roles.RoleDecls) := Plan roles × Sign

def entries (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) : List (Plan roles) :=
  (discover s.core.erased.current root).flatMap fun f =>
    atFocus (Encoded r) s root f (declChecked checked)

def questions (plans : List (Plan roles)) : List (Question roles) :=
  plans.map (·,.pass) ++ plans.map (·,.reject)

theorem of_focus (r : Registry) (s : State roles) (root f : Occurrence roles)
    (checked : (Boundary roles).Checked r)
    (generated : GeneralNominalSaturationState.Generated s.core.erased.current root f)
    (p : Plan roles) (present : p ∈ atFocus (Encoded r) s root f (declChecked checked)) :
    p ∈ entries r s root checked :=
  List.mem_flatMap.mpr ⟨f,(discover_exact ..).mpr generated,present⟩

theorem entries_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) :
    p ∈ entries r s root checked ↔
      ∃ f, GeneralNominalSaturationState.Generated s.core.erased.current root f ∧
        p ∈ atFocus (Encoded r) s root f (declChecked checked) := by
  constructor
  · intro member
    obtain ⟨f,listed,present⟩ := List.mem_flatMap.mp member
    exact ⟨f,(discover_exact ..).mp listed,present⟩
  · rintro ⟨f,generated,present⟩
    exact of_focus r s root f checked generated p present

theorem question_exact (plans : List (Plan roles)) (p : Plan roles) (sign : Sign) :
    (p,sign) ∈ questions plans ↔ p ∈ plans := by cases sign <;> simp [questions]

theorem question_count (plans : List (Plan roles)) :
    (questions plans).length = 2 * plans.length := by
  simp [questions,Nat.two_mul]

abbrev holds (s : State roles) (q : Question roles) (m : Assignment) : Prop :=
  Test s q.1 q.2 m

noncomputable def materialize (s : State roles) (plans : List (Plan roles)) : List Assignment :=
  samples (holds s) (questions plans)

theorem materialize_covers (s : State roles) (plans : List (Plan roles)) :
    Covers (holds s) (questions plans) (materialize s plans) :=
  GeneralRebaseFiniteWitnessTable297.covers (holds s) (questions plans)

theorem materialize_size (s : State roles) (plans : List (Plan roles)) :
    (materialize s plans).length ≤ 2 * plans.length := by
  rw [← question_count plans]
  exact GeneralRebaseFiniteWitnessTable297.length_le ..

/-- Executable aggregation of prior model and candidate replies.
A checked candidate bit is not evidence unless it uses the same old model. -/
def signed (prior : Assignment → Bool) (candidate : Plan roles → Assignment → Bool)
    (q : Question roles) (m : Assignment) : Bool :=
  prior m && match q.2 with
  | .pass => candidate q.1 m
  | .reject => !(candidate q.1 m)

structure Checked (s : State roles) (plans : List (Plan roles)) (xs : List Assignment)
    (prior : Assignment → Bool) (candidate : Plan roles → Assignment → Bool) : Prop where
  old : ∀ a ∈ xs, prior a = true ↔ Models s a
  test : ∀ p ∈ plans, ∀ a ∈ xs, candidate p a = true ↔ GeneralRebaseSignedModels297.Conditions s p a

theorem signed_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (check : Checked s plans xs prior candidate) (p : Plan roles) (listed : p ∈ plans)
    (sign : Sign) (a : Assignment) (found : a ∈ xs) :
    signed prior candidate (p,sign) a = true ↔ Test s p sign a := by
  cases sign with
  | pass => exact (Iff.of_eq (Bool.and_eq_true ..)).trans (and_congr (check.old a found) (check.test p listed a found))
  | reject =>
    have h : (!(candidate p a)) = true ↔ ¬ GeneralRebaseSignedModels297.Conditions s p a := by
      exact (Iff.of_eq (Bool.not_eq_true' _)).trans (Bool.eq_false_iff.trans (not_congr (check.test p listed a found)))
    exact (Iff.of_eq (Bool.and_eq_true ..)).trans (and_congr (check.old a found) h)

theorem exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs)
    (check : Checked s plans xs prior candidate) (p : Plan roles) (listed : p ∈ plans) (sign : Sign) :
    hit xs (signed prior candidate) (p,sign) = true ↔ ∃ m, Test s p sign m :=
  hit_exact _ _ _ cover _ _ ((question_exact plans p sign).mpr listed) (signed_exact check p listed sign)

end Yulang.GeneralRebaseSourceQuestions297
