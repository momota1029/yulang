import Yulang.CommonRoleStructuralDecomposition

/-! Model-exact generation of structural endpoint constraints across actual
variable paths, followed by payload decomposition. A single pass is not a
complete structural closure or satisfiability test. -/
namespace Yulang.CommonRolePathDecomposition
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonRoleStructuralPaths (Fact Path reach reach_exact path_subtype)

def join (paths : List (Fact n)) : Atom (Fin n) → Atom (Fin n) → List (Atom (Fin n))
  | .tyLe l (.var i), .tyLe (.var j) r =>
      if (i,j) ∈ paths then [.tyLe l r] else []
  | _, _ => []

theorem join_exact (paths : List (Fact n)) (x y z : Atom (Fin n)) :
    z ∈ join paths x y ↔ ∃ l r i j,
      x = .tyLe l (.var i) ∧ y = .tyLe (.var j) r ∧
      (i,j) ∈ paths ∧ z = .tyLe l r := by
  cases x with
  | rowLe => cases y <;> simp [join]
  | tyLe l mid =>
    cases mid <;> cases y <;> simp [join]
    case var.tyLe i mid r =>
      cases mid <;> simp
      case var j =>
        by_cases h : (i,j) ∈ paths <;> simp [h] <;> grind

def generated (atoms : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  atoms.flatMap fun x => atoms.flatMap fun y => join (reach atoms) x y

theorem generated_exact (atoms : List (Atom (Fin n))) (z : Atom (Fin n)) :
    z ∈ generated atoms ↔ ∃ l r i j,
      Atom.tyLe l (.var i) ∈ atoms ∧ Atom.tyLe (.var j) r ∈ atoms ∧
      Path atoms i j ∧ z = .tyLe l r := by
  simp only [generated, List.mem_flatMap, join_exact]
  constructor
  · rintro ⟨x,hx,y,hy,l,r,i,j,rfl,rfl,hp,rfl⟩
    exact ⟨l,r,i,j,hx,hy,(reach_exact ..).mp hp,rfl⟩
  · rintro ⟨l,r,i,j,hl,hr,hp,rfl⟩
    exact ⟨_,hl,_,hr,l,r,i,j,rfl,rfl,(reach_exact ..).mpr hp,rfl⟩

theorem generated_entailed (atoms : List (Atom (Fin n))) (a : Fin n → Comp Common.model)
    (models : All Common.model a atoms) : All Common.model a (generated atoms) := by
  intro z hz
  obtain ⟨l,r,i,j,hl,hr,hp,rfl⟩ := (generated_exact atoms z).mp hz
  exact Common.subtype_trans (models _ hl)
    (Common.subtype_trans (path_subtype atoms hp a models) (models _ hr))

def normalize (atoms : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  CommonRoleStructuralDecomposition.normalize (atoms ++ generated atoms)

theorem normalize_exact (atoms : List (Atom (Fin n))) (a : Fin n → Comp Common.model) :
    All Common.model a (normalize atoms) ↔ All Common.model a atoms := by
  rw [normalize, CommonRoleStructuralDecomposition.normalize_exact, PresenceNormalForm.all_append]
  exact ⟨And.left,fun h => ⟨h,generated_entailed atoms a h⟩⟩

/-- The pair endpoints are separated by slot 1; payload slot 0 has an incompatible lower bound. -/
def hidden : List (Atom (Fin 2)) :=
  [.tyLe (.pair (.base .int) (.var 0)) (.var 1),
   .tyLe (.var 1) (.pair (.base .int) (.base .bool)),
   .tyLe (.base .int) (.var 0)]

theorem hidden_old_false :
    CommonRoleRecursivePaths.check (CommonRoleStructuralDecomposition.normalize hidden) = false := by
  decide

theorem hidden_checked : CommonRoleRecursivePaths.check (normalize hidden) = true := by
  decide

theorem hidden_no_model (a : Fin 2 → Comp Common.model) : ¬ All Common.model a hidden := by
  intro h
  exact CommonRoleRecursivePaths.checked_no_model_all _ hidden_checked a
    ((normalize_exact _ a).mpr h)

end Yulang.CommonRolePathDecomposition
