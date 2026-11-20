import Yulang.GeneralRebaseMergeQuestions297
import Yulang.GeneralRebaseSignedIndex297

namespace Yulang.GeneralRebaseSourceWitnessProgram297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCandidates231 (HeadModels)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralNominalSaturationState (Generated)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseSourceQuestions297 (entries)
open GeneralRebaseSourceObserver267 (Probes installAt)
open GeneralRebaseSourceSelect267 (Guard)
open GeneralRebaseHeadProbe267 (Honest atFocus)
open GeneralRebaseFiniteWitnessTable297 (samples hit Covers)
open GeneralRebaseSignedModels297 (Conditions Sign Test)

abbrev Pair (roles : Roles.RoleDecls) := GeneralRebaseMergeQuestions297.Pair roles

def headTest (p : Plan roles) (m : Assignment) : Prop :=
  HeadModels p.packet.registry p.packet.context p.packet.site.occurrence p.packet.declaration p.packet.bounds m

inductive Question (roles : Roles.RoleDecls) where
 | head : Plan roles → Question roles
 | install : Plan roles → Sign → Question roles
 | mergeFailure : Pair roles → Question roles

def Holds (s : State roles) (q : Question roles) (m : Assignment) : Prop :=
 match q with
 | .head p => headTest p m
 | .install p sign => Test s p sign m
 | .mergeFailure pair => GeneralRebaseMergeQuestions297.counter s pair m

def registeredPairs (s : State roles) : List (Pair roles) :=
  s.core.sites.flatMap fun a => s.core.sites.map (fun b => (a,b))

theorem pairs_exact (s : State roles) (a b : Site roles) :
    (a,b) ∈ registeredPairs s ↔ a ∈ s.core.sites ∧ b ∈ s.core.sites := by
  unfold registeredPairs
  constructor
  · intro member
    obtain ⟨f,fm,inner⟩ := List.mem_flatMap.mp member
    obtain ⟨l,lm,eq⟩ := List.mem_map.mp inner
    cases eq
    exact ⟨fm,lm⟩
  · rintro ⟨one,two⟩
    exact List.mem_flatMap.mpr ⟨a,one,List.mem_map_of_mem two⟩

theorem pairs_size (s : State roles) :
    (registeredPairs s).length = s.core.sites.length * s.core.sites.length := by
  unfold registeredPairs
  generalize s.core.sites = sites
  have assisted (as : List (Site roles)) :
      (as.flatMap fun a => sites.map fun b => (a,b)).length = as.length * sites.length := by
    induction as with
    | nil => simp
    | cons a as ih => simp [ih,Nat.add_mul,Nat.add_comm]
  exact assisted sites

def questions (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) : List (Question roles) :=
  let ps := entries r s root checked
  (ps.map Question.head ++
    (GeneralRebaseSourceQuestions297.questions ps).map (fun q => .install q.1 q.2)) ++
    (registeredPairs s).map Question.mergeFailure

theorem head_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) (found : p ∈ entries r s root checked) :
    Question.head p ∈ questions r s root checked :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem found))

theorem install_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (p : Plan roles) (found : p ∈ entries r s root checked) (sign : Sign) :
    Question.install p sign ∈ questions r s root checked :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem ((GeneralRebaseSourceQuestions297.question_exact _ p sign).mpr found)))

theorem merge_listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (pair : Pair roles) (found : pair ∈ registeredPairs s) :
    Question.mergeFailure pair ∈ questions r s root checked :=
  List.mem_append_right _ (List.mem_map_of_mem found)

theorem questions_size (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    (questions r s root checked).length =
      3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length := by
  simp only [questions,List.length_append,List.length_map,GeneralRebaseSourceQuestions297.question_count,pairs_size]
  omega

structure Checks (roles : Roles.RoleDecls) where
  head : Plan roles → Assignment → Bool
  old : Assignment → Bool
  candidate : Plan roles → Assignment → Bool
  pair : Pair roles → Assignment → Bool

/-- 'pair' tests agreement in a single assignment, not equality in all
models; 'head' deliberately does not require this assignment to be old. -/
def mergeBit (c : Checks roles) (p : Pair roles) (a : Assignment) : Bool :=
  c.old a && !(c.pair p a)

def Observed (s : State roles) (xs : List Assignment) (plans : List (Plan roles))
    (c : Checks roles) : Prop :=
  (∀ p ∈ plans, ∀ a ∈ xs, c.head p a = true ↔ headTest p a) ∧
  GeneralRebaseSourceQuestions297.Checked s plans xs c.old c.candidate ∧
  ∀ p ∈ registeredPairs s, ∀ a ∈ xs, c.pair p a = true ↔ GeneralRebaseMergeQuestions297.atModel p a

theorem mergeBit_exact {s : State roles} {xs : List Assignment} {plans : List (Plan roles)} {c : Checks roles}
    (cert : Observed s xs plans c) (pair : Pair roles) (listed : pair ∈ registeredPairs s)
    (a : Assignment) (seen : a ∈ xs) :
    mergeBit c pair a = true ↔ GeneralRebaseMergeQuestions297.counter s pair a := by
  unfold mergeBit GeneralRebaseMergeQuestions297.counter
  rw [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff]
  exact and_congr (cert.2.1.old a seen) (not_congr (cert.2.2 pair listed a seen))

noncomputable def materialize (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) : List Assignment :=
  samples (Holds s) (questions r s root checked)

theorem materialize_covers (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    Covers (Holds s) (questions r s root checked) (materialize r s root checked) :=
  GeneralRebaseFiniteWitnessTable297.covers (Holds s) (questions r s root checked)

theorem materialize_size (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    (materialize r s root checked).length ≤
      3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length := by
  rw [← questions_size r s root checked]
  exact GeneralRebaseFiniteWitnessTable297.length_le (Holds s) (questions r s root checked)

def callbacks (xs : List Assignment) (c : Checks roles) : Probes roles :=
  GeneralRebaseSignedObserver297.withModels
    ⟨fun _ p => some (hit xs c.head p),fun _ _ => false,fun _ _ => false,
      fun a b => GeneralRebaseMergeQuestions297.equal xs (mergeBit c) (a,b)⟩
    xs c.old c.candidate

end Yulang.GeneralRebaseSourceWitnessProgram297
