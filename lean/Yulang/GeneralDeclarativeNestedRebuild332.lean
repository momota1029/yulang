import Yulang.GeneralDeclarativeNestedExample332
import Yulang.GeneralDeclarativeInlineAllocation331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedRebuild332
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)

mutual
/-- A normal target determines where to consume each concrete
occurrence. An actual read fixes this expression before we inspect
any model or child proposal; repeated binders remain separate slots. -/
def rebuild (pat : Expr) (uses : List Occurrence) : Option (Expr × List Occurrence) :=
  match pat with
  | .variable _ => uses.head?.map fun found => (found.term,uses.tail)
  | .primitive tag xs => (rebuildMany xs uses).map fun (many,left) => (.primitive tag many,left)
  | .nominal tag xs => (rebuildMany xs uses).map fun (many,left) => (.nominal tag many,left)
  | .variant tag p => (rebuild p uses).map fun (one,left) => (.variant tag one,left)
  | .record key p t => do
    let (one,remaining) ← rebuild p uses
    let (two,rest) ← rebuild t remaining
    pure (.record key one two,rest)
  | .join p t => do
    let (one,remaining) ← rebuild p uses
    let (two,rest) ← rebuild t remaining
    pure (.join one two,rest)
termination_by structural pat

def rebuildMany (pat : List Expr) (uses : List Occurrence) : Option (List Expr × List Occurrence) :=
  match pat with
  | [] => some ([],uses)
  | first::last => do
    let (one,remaining) ← rebuild first uses
    let (two,rest) ← rebuildMany last remaining
    pure (one::two,rest)
termination_by structural pat
end

theorem computed {mode} (traced : Walk mode raw pat uses) :
    ∀ after, rebuild pat (uses++after) = some (raw,after) := by
  refine Walk.rec
    (motive_1 := fun mode raw pat uses _ => ∀ after, rebuild pat (uses++after) = some (raw,after))
    (motive_2 := fun mode raw pat uses _ => ∀ after, rebuildMany pat (uses++after) = some (raw,after))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ traced
  · intros
    rfl
  · intro _ _ _ _ _ _ child after
    simp [rebuild,child after]
  · intro _ _ _ _ _ _ child after
    simp [rebuild,child after]
  · intro _ _ _ first _ _ last _ _ _ a b after
    simp [rebuild,List.append_assoc,a (last++after),b after]
  · intro _ _ _ _ _ _ one after
    simp [rebuild,one after]
  · intro _ _ _ first _ _ last _ _ a b after
    simp [rebuild,List.append_assoc,a (last++after),b after]
  · intros
    rfl
  · intro _ _ _ first _ _ last _ _ a b after
    simp [rebuildMany,List.append_assoc,a (last++after),b after]

theorem unique {mode} (first : Walk mode raw pat uses) (last : Walk mode other pat uses) : raw = other := by
  have one := computed first []
  have two := computed last []
  exact congrArg Prod.fst (Option.some.inj (one.symm.trans two))

end Yulang.GeneralDeclarativeNestedRebuild332
