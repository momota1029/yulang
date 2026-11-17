import Yulang.GeneralPresenceReadback245
import Yulang.CommonNominalFullGuardedClosure

/-! A guarded recursive Presence block has regular Common models for arbitrary
public parameters despite failing External and every strict source ranking.
Thus these sufficient representation guards are not language acceptance rules.
No source reachability or actual allocator transition is asserted here. -/
namespace Yulang.GeneralPresenceGuardedBlockLimit245
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceCrossRead244
open GeneralPresenceSubstitutionSupport244
open CommonNominalFullCarrier
open CommonNominalFullGuardedClosure

def body : Body 1 1 := fun _ => .pair (.inl 0) (.inr 0)

def solution (parameter : Ty) : Ty := instantiate body (fun _ => parameter) 0

theorem solution_equation (parameter : Ty) :
    Equivalent (solution parameter) (pair (solution parameter) parameter) := by
  exact all_parameter_sound body (fun _ => parameter) 0

def entries : List (Entry Nat) := [(2,.pair (.var 2) (.var 0))]

def extend (boundary : Nat → Comp model) (name : Nat) : Comp model :=
  if name = 2 then (solution (boundary 0).1,(boundary 2).2) else boundary name

theorem outside_preserved (boundary : Nat → Comp model) (name : Nat) (outside : name ≠ 2) :
    extend boundary name = boundary name := by simp [extend,outside]

theorem rows_preserved (boundary : Nat → Comp model) (name : Nat) :
    (extend boundary name).2 = (boundary name).2 := by
  by_cases same : name = 2
  · subst name; simp [extend]
  · simp [extend,same]

theorem block_satisfied (boundary : Nat → Comp model) :
    All model (extend boundary) (block entries) := by
  have same := solution_equation (boundary 0).1
  intro atom member
  simp only [entries,block,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    equations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simpa [Atom.Holds,TyTerm.eval,extend,model] using same.1
  · simpa [Atom.Holds,TyTerm.eval,extend,model] using same.2

theorem arbitrary_public_model (boundary : Nat → Comp model) :
    ∃ assignment, All model assignment (block entries) ∧
      (∀ name, name ≠ 2 → assignment name = boundary name) :=
  ⟨extend boundary,block_satisfied boundary,outside_preserved boundary⟩

theorem not_external : ¬ External entries := by
  intro external
  exact external (2,.pair (.var 2) (.var 0)) (by simp [entries])
    2 (by simp [typeSources]) (2,.pair (.var 2) (.var 0)) (by simp [entries]) rfl

theorem no_rank (rank : Nat → Nat) : ¬ RankedEntries rank entries := by
  intro ranked
  have lower := ranked (2,.pair (.var 2) (.var 0)) (by simp [entries]) 2 (by simp [typeSources])
  exact Nat.lt_irrefl _ lower

end Yulang.GeneralPresenceGuardedBlockLimit245
