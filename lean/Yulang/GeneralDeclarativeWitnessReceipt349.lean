import Yulang.GeneralDeclarativeWitnessEquation349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReceipt349
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def checks {A B : Type} (one : A → B → Bool) : List A → List B → Bool
  | [],[] => true
  | a::as,b::bs => one a b && checks one as bs
  | _,_ => false

theorem each {A B : Type} {one : A → B → Bool} {xs : List A} {ys : List B}
    (ok : checks one xs ys = true) :
    ∀ a ∈ xs, ∃ b ∈ ys, one a b = true := by
  induction xs generalizing ys with
  | nil => intro a empty; cases empty
  | cons x xs ih =>
    cases ys with
    | nil => cases ok
    | cons y ys =>
      have verified : (one x y && checks one xs ys) = true := ok
      obtain ⟨first,rest⟩ := splitAnd verified
      intro a used
      rcases List.mem_cons.mp used with rfl|last
      · exact ⟨y,List.mem_cons_self,first⟩
      · obtain ⟨b,located,same⟩ := ih rest a last
        exact ⟨b,List.mem_cons_of_mem _ located,same⟩

theorem exact_length {A B : Type} {one : A → B → Bool} {xs : List A} {ys : List B}
    (ok : checks one xs ys = true) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases ok
  | cons x xs ih =>
    cases ys with
    | nil => cases ok
    | cons y ys =>
      have verified : (one x y && checks one xs ys) = true := ok
      exact congrArg (· + 1) (ih (splitAnd verified).2)

theorem exact_position {A B : Type} {one : A → B → Bool} {xs : List A} {ys : List B}
    (ok : checks one xs ys = true) {i : Nat} {a : A} (x : xs[i]? = some a) :
    ∃ b, ys[i]? = some b ∧ one a b = true := by
  induction xs generalizing ys i with
  | nil => cases i <;> cases x
  | cons y rest ih =>
    cases ys with
    | nil => cases ok
    | cons z tail =>
      have verified : (one y z && checks one rest tail) = true := ok
      obtain ⟨here,later⟩ := splitAnd verified
      cases i with
      | zero =>
        have same : y = a := Option.some.inj x
        subst a
        exact ⟨z,rfl,here⟩
      | succ i =>
        obtain ⟨b,line,yes⟩ := ih later (i := i) x
        exact ⟨b,line,yes⟩

structure Plan where
  atoms : List Nat
  intervals : List GeneralDeclarativeWitnessBound349.Path
  equations : List GeneralDeclarativeWitnessEquation349.Code

/-- Each certificate entry belongs to one literal position of the
compiler state, including duplicate clauses or repeated equations. -/
def verify (expected current : State) (p : Plan) : Bool :=
  (checks (fun a ix => decide (current.normal.ordinary[ix]? = some a))
     expected.normal.ordinary p.atoms &&
   checks (fun pair => GeneralDeclarativeWitnessBound349.check current pair.1 pair.2)
     expected.normal.intervals p.intervals) &&
  checks (fun e => GeneralDeclarativeWitnessEquation349.check current (.variable e.left) e.right)
    expected.equations p.equations

theorem sound {expected current : State} {p : Plan} (ok : verify expected current p = true) :
    Receipt expected current := by
  have outer := splitAnd ok
  have inner := splitAnd outer.1
  refine ⟨?_,?_,?_⟩
  · intro a existing
    obtain ⟨ix,_,found⟩ := each inner.1 a existing
    exact List.mem_iff_getElem?.mpr ⟨ix,of_decide_eq_true found⟩
  · intro interval existing
    obtain ⟨_,_,found⟩ := each inner.2 interval existing
    exact GeneralDeclarativeWitnessBound349.sound found
  · intro e existing
    obtain ⟨_,_,found⟩ := each outer.2 e existing
    exact GeneralDeclarativeWitnessEquation349.sound found

theorem same_model {expected current : State} {p : Plan} (ok : verify expected current p = true)
    (m : GeneralNominalCommonBridge.Assignment) (fit : Models current m) : Models expected m :=
  relays_models (sound ok) m fit

end Yulang.GeneralDeclarativeWitnessReceipt349
