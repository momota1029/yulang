import Yulang.GeneralRebaseRawSafetyBits297

namespace Yulang.GeneralRebaseWitnessExistence297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseSourceWitnessProgram297 (Checks Observed headTest Holds Question questions materialize registeredPairs)
open GeneralRebaseSourceQuestions297 (entries)
open GeneralRebaseRawObserver297 (ExactSafety observe)
open GeneralRebaseFiniteWitnessTable297 (Covers)

noncomputable def flag (p : Prop) : Bool := Classical.propDecidable p |>.decide

theorem flag_exact (p : Prop) : flag p = true ↔ p := by
  unfold flag
  exact Iff.of_eq (@decide_eq_true_eq p (Classical.propDecidable p))

noncomputable def checks (s : State roles) : Checks roles :=
  ⟨fun p a => flag (headTest p a),fun a => flag (Models s a),
    fun p a => flag (GeneralRebaseSignedModels297.Conditions s p a),
    fun pair a => flag (GeneralRebaseMergeQuestions297.atModel pair a)⟩

theorem all_checked (s : State roles) (plans : List (Plan roles)) (xs : List Assignment) :
    Observed s xs plans (checks s) :=
  ⟨fun _ _ _ _ => flag_exact _,⟨fun _ _ => flag_exact _,fun _ _ _ _ => flag_exact _⟩,
    fun _ _ _ _ => flag_exact _⟩

/-- A finite exact certificate list exists for each source representative,
not one list for all states on a path. This choice does not find models,
synthesize K2 certificates, or compute an observation in the full carrier. -/
theorem finite_statement (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    ∃ xs : List Assignment, ∃ c : Checks roles,
      xs.length ≤ 3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length ∧
      Covers (Holds s) (questions r s root checked) xs ∧
        Observed s xs (entries r s root checked) c :=
  ⟨materialize r s root checked,checks s,GeneralRebaseSourceWitnessProgram297.materialize_size r s root checked,
    GeneralRebaseSourceWitnessProgram297.materialize_covers r s root checked,all_checked s _ _⟩

/-- Reuse one prior anchor between the two installation signs; head
witnesses may be outside the prior model set and are selected separately. -/
theorem smaller_pool (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) :
    ∃ xs : List Assignment, xs.length ≤
      2 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length + 1 ∧
      Covers (Holds s) (questions r s root checked) xs := by
  let ps := entries r s root checked
  let h := GeneralRebaseFiniteWitnessTable297.samples headTest ps
  let m := GeneralRebaseFiniteWitnessTable297.samples (GeneralRebaseMergeQuestions297.counter s) (registeredPairs s)
  obtain ⟨p,number,installCovers⟩ := GeneralRebaseWitnessAnchor297.exists_pool s ps
  let signed := GeneralRebasePriorWitness297.values p
  refine ⟨(h ++ signed) ++ m,?_,?_⟩
  · have sizeH := GeneralRebaseFiniteWitnessTable297.length_le headTest ps
    have sizeM := GeneralRebaseFiniteWitnessTable297.length_le
      (GeneralRebaseMergeQuestions297.counter s) (registeredPairs s)
    have upperM : m.length ≤ s.core.sites.length * s.core.sites.length :=
      GeneralRebaseSourceWitnessProgram297.pairs_size s ▸ sizeM
    have upperP : signed.length ≤ ps.length + 1 := by simpa [signed,GeneralRebasePriorWitness297.values] using number
    have upperH : h.length ≤ ps.length := sizeH
    change ((h ++ signed) ++ m).length ≤ 2 * ps.length + s.core.sites.length * s.core.sites.length + 1
    simp only [List.length_append]
    omega
  · intro q listed yes
    unfold questions at listed
    change q ∈ (ps.map Question.head ++
      (GeneralRebaseSourceQuestions297.questions ps).map (fun q => Question.install q.1 q.2)) ++
      (registeredPairs s).map Question.mergeFailure at listed
    rcases List.mem_append.mp listed with base | merge
    · rcases List.mem_append.mp base with hd | ins
      · obtain ⟨plan,mem,rfl⟩ := List.mem_map.mp hd
        obtain ⟨a,am,held⟩ := GeneralRebaseFiniteWitnessTable297.covers headTest ps plan mem yes
        exact ⟨a,List.mem_append_left _ (List.mem_append_left _ am),held⟩
      · obtain ⟨⟨plan,sign⟩,mem,rfl⟩ := List.mem_map.mp ins
        obtain ⟨a,am,held⟩ := installCovers (plan,sign) mem yes
        exact ⟨a,List.mem_append_left _ (List.mem_append_right _ am),held⟩
    · obtain ⟨pair,mem,rfl⟩ := List.mem_map.mp merge
      obtain ⟨a,am,held⟩ := GeneralRebaseFiniteWitnessTable297.covers (GeneralRebaseMergeQuestions297.counter s)
        (registeredPairs s) pair mem yes
      exact ⟨a,List.mem_append_right _ am,held⟩

/-- The classical existence statement additionally sources the independently
named safety gate without claiming it can be computed. -/
theorem finite_raw_observer (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (owners : List Nat) (pool : List Output) :
    ∃ xs : List Assignment, ∃ c : Checks roles, ∃ gate : Occurrence roles → Bool,
      xs.length ≤ 3 * (entries r s root checked).length + s.core.sites.length * s.core.sites.length ∧
      ∀ target,
        GeneralRebaseStep258.Step (observe r s root checked xs c gate owners pool)
          (GeneralRebaseLiveProjection264.project owners pool s) target ↔
        ∃ after, (Boundary roles).Step r root s after ∧
          GeneralRebaseLiveProjection264.project owners pool after = target ∧
          target ≠ GeneralRebaseLiveProjection264.project owners pool s := by
  obtain ⟨xs,c,bound,cover,checkedRows⟩ := finite_statement r s root checked
  let gate := fun f => flag (GeneralRebaseRawInstallScan297.Known r s f)
  have gateExact : ExactSafety r s root gate := fun _ _ => flag_exact _
  exact ⟨xs,c,gate,bound,GeneralRebaseRawObserver297.strict_exact reach metadata gateExact cover checkedRows owners pool⟩

end Yulang.GeneralRebaseWitnessExistence297
