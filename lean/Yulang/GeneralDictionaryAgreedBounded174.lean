import Yulang.GeneralDictionaryAgreedUniform174

/-! Structurally fuel-recursive outer diagnostic for a fixed frontier protocol.
Zero fuel uses a placeholder only: it is NOT a new language pending rule.
Exactness is asserted only with sufficient fuel, produced by certification.
Actual frontiers and final-state selection remain noncomputable; saturation
step counts and full compiler executability are not established. -/
namespace Yulang.GeneralDictionaryAgreedBounded174
open CommonRoleOutermostResolver

/-- Structural recursion with a semantically uninterpreted exhaustion fallback. -/
def runFuel (protocol : Protocol Request) : Nat → Request → Tree
  | 0, _ => .pending
  | fuel + 1, request =>
    match protocol.frontier request with
    | .pending => .pending
    | .ambiguous => .ambiguous
    | .rejected => .rejected
    | .selected key children => .selected key (children.map (runFuel protocol fuel))

/-- All generated children are traversed in order; no diagnostic is short-circuited. -/
theorem runFuel_resolves (protocol : Protocol Request) (exact : FrontierExact protocol)
    (rank : Request → Nat)
    (decreases : ∀ {child parent}, Child protocol.Local child parent → rank child < rank parent)
    (fuel : Nat) (request : Request) (enough : rank request < fuel) :
    Resolves protocol.Local request (runFuel protocol fuel request) := by
  induction fuel generalizing request with
  | zero => omega
  | succ fuel ih =>
    simp only [runFuel]
    split
    next observed => exact .pending ((exact request _).mp observed)
    next observed => exact .ambiguous ((exact request _).mp observed)
    next observed => exact .rejected ((exact request _).mp observed)
    next key children observed =>
      have localRule := (exact request _).mp observed
      apply Resolves.selected localRule
      have each (child : Request) (member : child ∈ children) :
          Resolves protocol.Local child (runFuel protocol fuel child) := by
        have decrease := decreases ⟨key, children, localRule, member⟩
        exact ih child (by omega)
      clear observed localRule
      induction children with
      | nil => exact .nil
      | cons child children childIH =>
        exact .cons (each child (by simp))
          (childIH (fun c mem => each c (List.mem_cons_of_mem _ mem)))

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal B4TargetV5
open GeneralDictionaryAgreedGround174 GeneralDictionaryAgreedUniform174
open GeneralDictionaryAgreedComputed174 GeneralDictionaryAgreedEdge174
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

/-- A certified declaration graph supplies the rank internally. This concerns
any fixed state whose frontier protocol is exact, not saturation termination. -/
theorem certified_resolves (passed : certify registry = true)
    (exact : FrontierExact (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state)) :
    Resolves (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state).Local root
      (runFuel (GeneralNominalActualAgreedBoundary.frontiers defer gap registry state)
        ((roleNodes registry).length + 1) root) := by
  apply runFuel_resolves _ exact
    (fun occurrence => computedHeight registry (roleNodes registry).length occurrence.demand.role)
  · rintro child parent ⟨key, children, selected, member⟩
    apply child_role_decreases (check_sound passed)
    exact ⟨key, children,
      (GeneralNominalActualAgreedBoundary.local_correspondence defer gap registry state parent _).mp selected,
      member⟩
  · have bound := computedHeight_le_fuel registry (roleNodes registry).length root.demand.role
    omega

/-- Uniform finite recursion agrees with the existing ground final diagnostic.
There is no manual rank, Acc, or runtime fuel premise. -/
theorem certified_final_eq (checked : (boundary defer gap).Checked registry)
    (passed : certify registry = true)
    (reachable : Reachable (boundary defer gap) registry root state) :
    runFuel (GeneralNominalActualAgreedBoundary.frontiers defer gap registry
      ((executor defer gap).run registry state root).1) ((roleNodes registry).length + 1) root =
      ((executor defer gap).run registry state root).2 := by
  have resolved := certified_resolves (root := root) passed
    (GeneralDictionaryAgreedExact174.final_exact checked reachable)
  exact ((certified_run_resolves_iff checked passed reachable _).mpr resolved).symm

end Yulang.GeneralDictionaryAgreedBounded174
