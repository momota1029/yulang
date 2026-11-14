import Yulang.GeneralDictionaryAgreedChecked174
import Yulang.GeneralDictionaryAgreedSearchOrder174

/-! A finite complete search bound for the role-DAG certificate checker.
This recognizes a restricted syntactic fragment, not all valid declarations.
Duplicates in the role list enlarge the bound but do not affect soundness.
Neither certificate search nor its failure is a language evaluation rule. -/
namespace Yulang.GeneralDictionaryAgreedUniform174
open GeneralDeclarations GeneralDictionaryAgreedComputed174 GeneralDictionaryAgreedEdge174

def roleNodes (registry : Registry) : List Nat :=
  registry.declarations.flatMap fun declaration =>
    declaration.role :: declaration.requirements.map (·.role)

def belowCount (rank : Nat → Nat) (bound : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if rank x < bound then 1 else 0) + belowCount rank bound xs

theorem belowCount_le_length (rank : Nat → Nat) (bound : Nat) (nodes : List Nat) :
    belowCount rank bound nodes ≤ nodes.length := by
  induction nodes with
  | nil => simp [belowCount]
  | cons x xs ih =>
    simp only [belowCount, List.length_cons]
    split <;> omega

theorem belowCount_mono (rank : Nat → Nat) (nodes : List Nat) (less : a ≤ b) :
    belowCount rank a nodes ≤ belowCount rank b nodes := by
  induction nodes with
  | nil => simp [belowCount]
  | cons x xs ih =>
    simp only [belowCount]
    split <;> split <;> omega

theorem belowCount_strict (rank : Nat → Nat) (nodes : List Nat)
    (present : child ∈ nodes) (less : rank child < bound) :
    belowCount rank (rank child) nodes < belowCount rank bound nodes := by
  induction nodes with
  | nil => cases present
  | cons x xs ih =>
    rcases List.mem_cons.mp present with same | member
    · subst x
      have mono := belowCount_mono rank xs (Nat.le_of_lt less)
      simp only [belowCount, Nat.lt_irrefl, ↓reduceIte, less]
      omega
    · have strict := ih member
      simp only [belowCount]
      split <;> split <;> omega

theorem child_mem_nodes (visible : declaration ∈ registry.declarations)
    (member : clause ∈ declaration.requirements) : clause.role ∈ roleNodes registry := by
  apply List.mem_flatMap.mpr
  refine ⟨declaration, visible, ?_⟩
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨clause,member,rfl⟩)

def compressedRank (registry : Registry) (rank : Nat → Nat) (role : Nat) : Nat :=
  belowCount rank (rank role) (roleNodes registry)

theorem compressed_stratified (stratified : RoleStratified registry rank) :
    RoleStratified registry (compressedRank registry rank) := by
  intro declaration visible clause member
  exact belowCount_strict rank _ (child_mem_nodes visible member)
    (stratified declaration visible clause member)

theorem uniform_complete (stratified : RoleStratified registry rank) :
    check registry (roleNodes registry).length = true := by
  apply check_complete (compressed_stratified stratified)
  intro declaration _
  exact belowCount_le_length rank _ _

/-- Complete executable recognition of the role-DAG fragment. -/
def certify (registry : Registry) : Bool := check registry (roleNodes registry).length

theorem certify_iff : certify registry = true ↔ ∃ rank, RoleStratified registry rank := by
  constructor
  · intro passed
    exact ⟨_,check_sound passed⟩
  · rintro ⟨rank,stratified⟩
    exact uniform_complete stratified

theorem certify_reorders (order : GeneralRegistryReordering.Reorders first last) :
    certify first = certify last := by
  have truth : certify first = true ↔ certify last = true := by
    rw [certify_iff, certify_iff]
    exact exists_congr (fun rank =>
      GeneralDictionaryAgreedSearchOrder174.stratified_reorders_iff order rank)
  cases a : certify first <;> cases b : certify last <;> simp_all

open GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalActualAgreedLocal CommonRoleOutermostResolver B4TargetV5
open GeneralDictionaryAgreedGround174
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root : Occurrence roles}

/-- No search-fuel or rank argument remains in this exactness interface. -/
theorem certified_run_resolves_iff (checked : (boundary defer gap).Checked registry)
    (passed : certify registry = true)
    (reachable : Reachable (boundary defer gap) registry root state) (tree : Tree) :
    ((executor defer gap).run registry state root).2 = tree ↔
      Resolves (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1) root tree :=
  GeneralDictionaryAgreedChecked174.run_resolves_iff checked passed reachable tree

theorem certified_completed_iff (checked : (boundary defer gap).Checked registry)
    (passed : certify registry = true)
    (reachable : Reachable (boundary defer gap) registry root state) (out : Result) :
    B4TargetV3.Completed ((executor defer gap).run registry state root).2 out ↔
      B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1 root out :=
  GeneralDictionaryAgreedChecked174.completed_iff checked passed reachable out

theorem wrap_certified : certify GeneralDictionaryAgreedRoleExamples174.wrapOnly = true := by
  decide +kernel

theorem recursive_not_certified : certify GeneralDeclarationExamples.registry = false := by
  exact display_fails _

theorem computedHeight_le_fuel (registry : Registry) (fuel role : Nat) :
    computedHeight registry fuel role ≤ fuel := by
  induction fuel generalizing role with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    apply (GeneralDictionaryAgreedSearchOrder174.fold_max_le_iff _ _ _ _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro child _
    exact Nat.succ_le_succ (ih child)

/-- Every selected-child path has an explicit finite depth bound in the
certified fragment. This does not count saturation steps or tree width. -/
theorem certified_descent_bound (passed : certify registry = true)
    (path : Descent defer gap registry state root depth child) :
    depth ≤ (roleNodes registry).length := by
  have bounded := descent_bounded (check_sound passed) path
  have height := computedHeight_le_fuel registry (roleNodes registry).length root.demand.role
  omega

end Yulang.GeneralDictionaryAgreedUniform174
