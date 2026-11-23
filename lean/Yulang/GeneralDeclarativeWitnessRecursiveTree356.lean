import Yulang.GeneralDeclarativeWitnessRecursiveMixed356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecursiveTree356
open GeneralDeclarativeWitnessRecursiveMixed356 (Tree Branches)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row)
open GeneralDeclarativeWitnessSpineNode355 (Node)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWitnessTree349 (exact_report)
open CommonRoleOutermostResolver (Dictionary Result classification classifications classification_exact classifications_exact)

mutual
def view {s : State} {e p} (t : @Tree s e p) : CommonRoleOutermostResolver.Tree :=
  match t with
  | .typed _ xs => .selected p.name (views xs)
termination_by sizeOf t

def views {s : State} {e p i ds} (ts : @Branches s e p i ds) : List CommonRoleOutermostResolver.Tree :=
  match ts with
  | .nil => []
  | .typed _ below tail => view below :: views tail
  | .payload _ c tail => c.actual.diagnostic.tree :: views tail
termination_by sizeOf ts
end

mutual
def dictionary {s : State} {e p} (t : @Tree s e p) : Dictionary :=
  match t with
  | .typed _ xs => .node p.name (dictionaries xs)
termination_by sizeOf t

def dictionaries {s : State} {e p i ds} (ts : @Branches s e p i ds) : List Dictionary :=
  match ts with
  | .nil => []
  | .typed _ below tail => dictionary below :: dictionaries tail
  | .payload _ c tail => c.dictionary :: dictionaries tail
termination_by sizeOf ts
end

mutual
def rows {s : State} {e p} (t : @Tree s e p) : List Row :=
  match t with
  | .typed _ xs => p.input.rows ++ otherRows xs
termination_by sizeOf t

def otherRows {s : State} {e p i ds} (ts : @Branches s e p i ds) : List Row :=
  match ts with
  | .nil => []
  | .typed _ below tail => rows below ++ otherRows tail
  | .payload _ _ tail => otherRows tail
termination_by sizeOf ts
end

theorem exact_tree {s : State} {e p} (t : @Tree s e p) :
    classification (view t) = .selected (dictionary t) := by
  refine @Tree.rec s e
    (fun _ tree => classification (view tree) = .selected (dictionary tree))
    (fun _ _ _ branches => classifications (views branches) = (dictionaries branches).map Result.selected)
    ?_ ?_ ?_ ?_ p t
  · intro p role c ih
    rw [view.eq_def,dictionary.eq_def]
    exact (classification_exact ..).mpr (.selected ((classifications_exact ..).mp ih) (.selected rfl))
  · intro i p
    rw [views.eq_def,dictionaries.eq_def]
    rfl
  · intro i d ds p a w edge below tail more rest
    rw [views.eq_def,dictionaries.eq_def,List.map_cons]
    change classification (view below) :: classifications (views tail) =
      .selected (dictionary below) :: _
    rw [more,rest]
  · intro i d ds p r projection observed tail rest
    rw [views.eq_def,dictionaries.eq_def,List.map_cons]
    change classification observed.actual.diagnostic.tree :: classifications (views tail) = .selected observed.dictionary :: _
    have found := (exact_report observed.actual.exactResult).2.1.symm.trans observed.exactDict
    rw [found,rest]

end Yulang.GeneralDeclarativeWitnessRecursiveTree356
