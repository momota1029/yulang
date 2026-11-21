import Yulang.GeneralDeclarativeCaptureClosure320
import Yulang.GeneralDeclarativeNewNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshTerms324
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames typeSources type_eval_same preserves_models)
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models)
open GeneralDeclarativeNewNames321 (after before_after)
open GeneralDeclarativeMerge320 (EqualTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model subtype_refl)

def protectedNames (s : State) (keep : List Nat) (a b : TyTerm Nat) : List Nat :=
  ((stateNames s ++ keep) ++ typeSources a) ++ typeSources b

def first (s : State) (keep : List Nat) (a b : TyTerm Nat) : Nat :=
  after (protectedNames s keep a b)
def second (s : State) (keep : List Nat) (a b : TyTerm Nat) : Nat :=
  first s keep a b + 1

def equations (s : State) (keep : List Nat) (a b : TyTerm Nat) : List (Atom Nat) :=
  [.tyLe (.var (first s keep a b)) a,.tyLe a (.var (first s keep a b)),
   .tyLe (.var (second s keep a b)) b,.tyLe b (.var (second s keep a b))]

def updated (s : State) (keep : List Nat) (a b : TyTerm Nat) : State :=
  withOrdinary s (equations s keep a b)

def extend (s : State) (keep : List Nat) (a b : TyTerm Nat) (m : Assignment) : Assignment := fun n =>
  if n = first s keep a b then (a.eval model m,(m n).2)
  else if n = second s keep a b then (b.eval model m,(m n).2)
  else m n

theorem protected_same {s : State} {keep : List Nat} {a b : TyTerm Nat} (m : Assignment)
    (listed : n ∈ protectedNames s keep a b) : extend s keep a b m n = m n := by
  have prior : n < first s keep a b := before_after listed
  simp [extend, Nat.ne_of_lt prior, show n ≠ second s keep a b by unfold second; omega]

theorem first_value (s : State) (keep : List Nat) (a b : TyTerm Nat) (m : Assignment) :
    (extend s keep a b m (first s keep a b)).1 = a.eval model m := by simp [extend]

theorem second_value (s : State) (keep : List Nat) (a b : TyTerm Nat) (m : Assignment) :
    (extend s keep a b m (second s keep a b)).1 = b.eval model m := by
  have distinct : second s keep a b ≠ first s keep a b := by unfold second; omega
  simp [extend,distinct]

theorem written_holds {s : State} (keep : List Nat) (a b : TyTerm Nat) (m : Assignment) :
    All model (extend s keep a b m) (equations s keep a b) := by
  have av : a.eval model (extend s keep a b m) = a.eval model m :=
    type_eval_same a (fun n h => protected_same m (List.mem_append_left _ (List.mem_append_right _ h)))
  have bv : b.eval model (extend s keep a b m) = b.eval model m :=
    type_eval_same b (fun n h => protected_same m (List.mem_append_right _ h))
  intro atom used
  simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl|rfl
  all_goals
    simp only [Atom.Holds,TyTerm.eval,first_value,second_value,av,bv]
    exact subtype_refl _

/-- Defining the two aggregates is model-conservative over the original
ordinary constraints, all read operands, and all caller-protected
logical names. Existing associated targets are not narrowed by this. -/
theorem projection {s : State} (keep : List Nat) (a b : TyTerm Nat) (m : Assignment) :
    Models s m ↔ ∃ new, Models (updated s keep a b) new ∧
      ∀ n ∈ protectedNames s keep a b, new n = m n := by
  constructor
  · intro valid
    have kept := fun n h => protected_same (s := s) (keep := keep) (a := a) (b := b) m (n := n) h
    have modelsOld := (preserves_models s
      (fun n h => kept n (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))).mpr valid
    exact ⟨extend s keep a b m,(ordinary_models _).mpr ⟨modelsOld,written_holds keep a b m⟩,kept⟩
  · rintro ⟨new,got,kept⟩
    exact (preserves_models s
      (fun n h => kept n (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))).mp
      ((ordinary_models new).mp got).1

theorem actual_rows (s : State) (keep : List Nat) (a b : TyTerm Nat) :
    EqualTerm (updated s keep a b) (first s keep a b) a ∧
    EqualTerm (updated s keep a b) (second s keep a b) b := by
  have one : ∀ row ∈ equations s keep a b, row ∈ (updated s keep a b).normal.ordinary :=
    fun _ found => List.mem_append_right _ found
  exact ⟨⟨one _ (by simp [equations]),one _ (by simp [equations])⟩,
    ⟨one _ (by simp [equations]),one _ (by simp [equations])⟩⟩

end Yulang.GeneralDeclarativeFreshTerms324
