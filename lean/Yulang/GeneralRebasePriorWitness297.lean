import Yulang.GeneralRebaseSignedSupport297

namespace Yulang.GeneralRebasePriorWitness297
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSignedModels297 (Sign Conditions Test)
open GeneralRebaseSignedSupport297 (Agree candidateReads on_prior_models)
open GeneralRebaseSourceQuestions297 (Question holds questions)
open GeneralRebaseFiniteWitnessTable297 (Covers)

abbrev Prior (s : State roles) := {m : Assignment // Models s m}

def values {s : State roles} (pool : List (Prior s)) : List Assignment := pool.map Subtype.val

/-- A typed representation sufficient for both signs. Raw conversion of
the world state is not required when both assignments have prior certificates. -/
def Represents (s : State roles) (plans : List (Plan roles)) (pool : List (Prior s)) : Prop :=
  ∀ p ∈ plans, ∀ a : Prior s, ∃ b ∈ pool, Agree (candidateReads s p) a.val b.val

theorem covers {s : State roles} {plans : List (Plan roles)} {pool : List (Prior s)}
    (rep : Represents s plans pool) : Covers (holds s) (questions plans) (values pool) := by
  rintro ⟨p,sign⟩ present ⟨a,valid⟩
  have pMem := (GeneralRebaseSourceQuestions297.question_exact plans p sign).mp present
  obtain ⟨b,listed,agree⟩ := rep p pMem ⟨a,valid.1⟩
  exact ⟨b.val,List.mem_map_of_mem listed,
    (on_prior_models s p sign a b.val valid.1 b.property agree).mp valid⟩

theorem prior_exact {s : State roles} (pool : List (Prior s)) (a : Assignment)
    (used : a ∈ values pool) : Models s a := by
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp used
  exact b.property

def vote {s : State roles} (pool : List (Prior s)) (check : Plan roles → Prior s → Bool)
    (p : Plan roles) (sign : Sign) : Bool :=
  pool.any fun a => match sign with
  | .pass => check p a
  | .reject => !(check p a)

/-- The finite OR is executable over already checked rows; the arbitrary
source does not get a decision procedure for finding or checking those rows. -/
theorem vote_exact {s : State roles} {plans : List (Plan roles)} {pool : List (Prior s)}
    (cover : Covers (holds s) (questions plans) (values pool))
    (check : Plan roles → Prior s → Bool) (p : Plan roles) (listed : p ∈ plans)
    (cert : ∀ a ∈ pool, check p a = true ↔ Conditions s p a.val) (sign : Sign) :
    vote pool check p sign = true ↔ ∃ m, Test s p sign m := by
  unfold vote
  rw [List.any_eq_true]
  have one (a : Prior s) (mem : a ∈ pool) : (match sign with
      | .pass => check p a
      | .reject => !(check p a)) = true ↔ Test s p sign a.val := by
    cases sign
    · exact (cert a mem).trans ⟨fun h => ⟨a.property,h⟩,And.right⟩
    · rw [Bool.not_eq_true',Bool.eq_false_iff]
      exact (not_congr (cert a mem)).trans ⟨fun h => ⟨a.property,h⟩,And.right⟩
  constructor
  · rintro ⟨a,used,h⟩
    exact ⟨a.val,(one a used).mp h⟩
  · intro h
    obtain ⟨a,used,holds⟩ := cover (p,sign) ((GeneralRebaseSourceQuestions297.question_exact plans p sign).mpr listed) h
    obtain ⟨b,inPool,rfl⟩ := List.mem_map.mp used
    exact ⟨b,inPool,(one b inPool).mpr holds⟩

end Yulang.GeneralRebasePriorWitness297
