import Yulang.GeneralDeclarativeWitnessProjectionCheck358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOrderedReplay358
open GeneralDeclarativeWitnessDeclaredState357 (Current)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessProjectionCheck358 (Certificate)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer Layout)
open GeneralDeclarativeWitnessCompiler350 (Wire)
open GeneralDeclarativeDemand320 (Demand)

inductive LocalCode where
  | join (plan : GeneralDeclarativeWitnessJoinedCheck357.Recipe)
  | project (plan : GeneralDeclarativeWitnessAuthoredProjection358.Recipe) (binder : Nat)

inductive Local (source : Source) (s : Current) (d : Demand) where
  | joined {wire : Wire} : Answer s d wire → Local source s d
  | projection {wire : Wire} : Certificate source s d wire → Local source s d

def Local.key {src s d} : Local src s d → Nat
  | .joined a => a.impl.id
  | .projection a => a.impl.id

def Local.kids {src s d} : Local src s d → List Demand
  | .joined a => a.kids
  | .projection a => a.kids

def localRead (source : Source) (s : Current) (d : Demand) (layout : Layout)
    (code : LocalCode) (wire : Wire) : Option (Local source s d) :=
  match code with
  | .join recipe =>
    (GeneralDeclarativeWitnessJoinedCheck357.replay s d recipe layout wire).map .joined
  | .project recipe binder =>
    (GeneralDeclarativeWitnessProjectionCheck358.replay source s d recipe binder layout wire).map .projection

mutual
inductive Code where
  | node : LocalCode → Wire → Codes → Code
inductive Codes where
  | nil
  | cons : Code → Codes → Codes
end

mutual
inductive Tree (a : Source) (s : Current) : List Nat → Demand → Type where
  | node (head : Local a s d) (children : Forest a s p 0 head.kids) : Tree a s p d
inductive Forest (a : Source) (s : Current) : List Nat → Nat → List Demand → Type where
  | nil : Forest a s path i []
  | cons : Tree a s (path ++ [i]) d → Forest a s path (i+1) ds → Forest a s path i (d::ds)
end

abbrev LayoutAt := List Nat → Layout

mutual
def read (a : Source) (s : Current) (layout : LayoutAt) (path : List Nat) (d : Demand) :
    Code → Option (Tree a s path d)
  | .node method packet children => do
    let head ← localRead a s d (layout path) method packet
    let later ← readList a s layout path 0 head.kids children
    pure (.node head later)
termination_by code => sizeOf code

def readList (a : Source) (s : Current) (layout : LayoutAt) (path : List Nat) (index : Nat)
    (d : List Demand) : Codes → Option (Forest a s path index d)
  | .nil => match d with
    | [] => some .nil
    | _ => none
  | .cons next rest => match d with
    | [] => none
    | first::after => do
      let head ← read a s layout (path ++ [index]) first next
      let last ← readList a s layout path (index+1) after rest
      pure (.cons head last)
termination_by code => sizeOf code
end

end Yulang.GeneralDeclarativeWitnessOrderedReplay358
