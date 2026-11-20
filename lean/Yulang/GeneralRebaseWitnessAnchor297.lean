import Yulang.GeneralRebasePriorWitness297

namespace Yulang.GeneralRebaseWitnessAnchor297
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebasePriorWitness297 (Prior values)
open GeneralRebaseSignedModels297 (Conditions Test Sign)
open GeneralRebaseSourceQuestions297 (Question holds questions)
open GeneralRebaseFiniteWitnessTable297 (samples Covers)

def Differs (s : State roles) (anchor : Prior s) (p : Plan roles) (b : Prior s) : Prop :=
  ¬ (Conditions s p anchor.val ↔ Conditions s p b.val)

noncomputable def around {s : State roles} (plans : List (Plan roles)) (a : Prior s) : List (Prior s) :=
  a :: samples (Differs s a) plans

theorem at_most_succ {s : State roles} (plans : List (Plan roles)) (a : Prior s) :
    (around plans a).length ≤ plans.length + 1 :=
  Nat.succ_le_succ (GeneralRebaseFiniteWitnessTable297.length_le (Differs s a) plans)

theorem around_covers {s : State roles} (plans : List (Plan roles)) (a : Prior s) :
    Covers (holds s) (questions plans) (values (around plans a)) := by
  classical
  rintro ⟨p,sg⟩ asked ⟨b,found⟩
  have plan := (GeneralRebaseSourceQuestions297.question_exact plans p sg).mp asked
  by_cases chosen : Test s p sg a.val
  · exact ⟨a.val,List.mem_map_of_mem (List.mem_cons_self ..),chosen⟩
  · have differing : Differs s a p ⟨b,found.1⟩ := by
      intro e
      apply chosen
      cases sg
      · exact ⟨a.property,e.mpr found.2⟩
      · exact ⟨a.property,fun h => found.2 (e.mp h)⟩
    obtain ⟨c,listed,changeSide⟩ :=
      GeneralRebaseFiniteWitnessTable297.covers (Differs s a) plans p plan ⟨⟨b,found.1⟩,differing⟩
    refine ⟨c.val,List.mem_map_of_mem (List.mem_cons_of_mem _ listed),c.property,?_⟩
    cases sg with
    | pass =>
      apply Classical.byContradiction
      intro no
      exact changeSide ⟨fun h => False.elim (chosen ⟨a.property,h⟩),
        fun h => False.elim (no h)⟩
    | reject =>
      intro yes
      exact changeSide ⟨fun _ => yes,fun _ => Classical.byContradiction (fun notA => chosen ⟨a.property,notA⟩)⟩

theorem exists_pool (s : State roles) (plans : List (Plan roles)) :
    ∃ pool : List (Prior s), pool.length ≤ plans.length + 1 ∧
      Covers (holds s) (questions plans) (values pool) := by
  classical
  by_cases old : ∃ m, Models s m
  · obtain ⟨a,valid⟩ := old
    exact ⟨around plans ⟨a,valid⟩,at_most_succ plans _,around_covers plans _⟩
  · exact ⟨[],Nat.zero_le _,fun _ _ ⟨m,found⟩ => False.elim (old ⟨m,found.1⟩)⟩

/-- A nonempty reply requires a prior model, and when both signs occur
one row can never suffice. Completeness is checked over the same list. -/
theorem opposed_requires_two {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    (cover : Covers (holds s) (questions plans) xs) (p : Plan roles) (listed : p ∈ plans)
    (yes : ∃ a, Test s p .pass a) (no : ∃ a, Test s p .reject a) :
    2 ≤ xs.length := by
  obtain ⟨a,am,ap⟩ := cover (p,.pass) ((GeneralRebaseSourceQuestions297.question_exact ..).mpr listed) yes
  obtain ⟨b,bm,bp⟩ := cover (p,.reject) ((GeneralRebaseSourceQuestions297.question_exact ..).mpr listed) no
  have separate : a ≠ b := fun eq => GeneralRebaseSignedModels297.exclusive s p a ⟨ap,eq.symm ▸ bp⟩
  have uniq : ([a,b] : List Assignment).Nodup := by simp [separate]
  have inside : ([a,b] : List Assignment) ⊆ xs := by
    intro m present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl <;> assumption
  exact List.Nodup.length_le_of_subset uniq inside

end Yulang.GeneralRebaseWitnessAnchor297
