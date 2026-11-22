import Yulang.GeneralDeclarativeNestedDecode332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedIndex332
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def direct (rows : List Equation) (n : Nat) : Option Expr :=
  (rows.find? fun e => e.left == n).map Equation.right

theorem direct_exact (reads : direct rows n = some rhs) : (⟨n,rhs⟩ : Equation) ∈ rows := by
  unfold direct at reads
  cases seen : List.find? (fun e : Equation => e.left == n) rows with
  | none => simp [seen] at reads
  | some e =>
    have packed := List.find?_some seen
    have found := List.mem_of_find?_eq_some seen
    rcases e with ⟨owner,raw⟩
    have reaches : owner = n := by simpa using packed
    have spells : raw = rhs := by simpa [seen] using reads
    cases reaches
    cases spells
    exact found

/-- The supplied list is an independently gathered finite selection
of already supported rows. It may be ordered to select the intended
spelling; the first hit is not a completeness or acceptance rule. -/
def ofRows {s : State} (rows : List Equation) (valid : rows ⊆ s.equations) : Sources s :=
  ⟨direct rows,fun n rhs hit => ⟨n,alias_refl _,valid (direct_exact hit)⟩,
    fun _ => none,fun _ _ _ impossible => by cases impossible⟩

/-- An alias index can reuse exactly the same syntactic producer.
Each input redirection has a proof from the available alias relation;
the snapshot does not search a recursion graph or infer authority. -/
def withAliases {s : State} (rows : List Equation) (valid : rows ⊆ s.equations)
    (target : Nat → Nat) (ground : ∀ n, Alias s n (target n)) : Sources s :=
  ⟨fun n => direct rows (target n),fun n rhs hit => ⟨target n,ground n,valid (direct_exact hit)⟩,
    fun _ => none,fun _ _ _ impossible => by cases impossible⟩

end Yulang.GeneralDeclarativeNestedIndex332
