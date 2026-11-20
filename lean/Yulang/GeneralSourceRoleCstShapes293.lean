import Yulang.GeneralSourceRoleCstTree293

/-! Extract only rooted, unqualified role heads and bare associated forms.
Both token kind and ownership matter; no source name is resolved here. -/
namespace Yulang.GeneralSourceRoleCstShapes293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleHeadShape292 (Head Primary Argument)
open GeneralSourceRoleSyntaxBoundary292 (Shape Rhs)
open GeneralSourceRoleExport292 (collect collect_exact Aligned)

def visible (cs : List Tree) : List Tree := (significant cs).map Prod.snd

mutual
def cleanTree : Tree → Bool
  | .node k cs => decide (k ≠ .missing ∧ k ≠ .invalid ∧ k ≠ .error) && cleanList cs
  | .token k _ => decide (k ≠ .missing ∧ k ≠ .invalid ∧ k ≠ .error)
def cleanList : List Tree → Bool
  | [] => true
  | a::as => cleanTree a && cleanList as
end

def argumentName : Tree → Option String
  | .node .argument cs =>
    match visible cs with
    | [.token .sigilIdentifier s] => some s
    | _ => none
  | _ => none

def HasArgument (t : Tree) (s : String) : Prop :=
  ∃ cs, t = .node .argument cs ∧ visible cs = [.token .sigilIdentifier s]

theorem argument_exact (t : Tree) (s : String) : argumentName t = some s ↔ HasArgument t s := by
  constructor
  · intro eq
    cases t with
    | token => cases eq
    | node k cs =>
      cases k <;> try cases eq
      cases h : visible cs with
      | nil => simp [argumentName,h] at eq
      | cons first rest =>
        cases rest with
        | cons extra tail =>
          cases first <;> simp [argumentName,h] at eq
        | nil =>
          cases first with
          | node => simp [argumentName,h] at eq
          | token k text =>
            cases k <;> simp [argumentName,h] at eq
            subst text
            exact ⟨cs,rfl,h⟩
  · rintro ⟨cs,rfl,e⟩
    simp [argumentName,e]

def headView : Tree → Option (String × List String)
  | .node .head cs =>
    match visible cs with
    | .token .identifier name :: args => (collect argumentName args).map (name, ·)
    | _ => none
  | _ => none

def HasHead (t : Tree) (n : String) (parameters : List String) : Prop :=
  ∃ cs args, t = .node .head cs ∧ visible cs = .token .identifier n :: args ∧
    Aligned HasArgument args parameters

theorem head_exact (t : Tree) (name : String) (params : List String) :
    headView t = some (name,params) ↔ HasHead t name params := by
  constructor
  · intro resolved
    cases t with
    | token => cases resolved
    | node k cs =>
      cases k <;> try cases resolved
      cases h : visible cs with
      | nil => simp [headView,h] at resolved
      | cons first args =>
        cases first with
        | node => simp [headView,h] at resolved
        | token k s =>
          cases k <;> simp [headView,h] at resolved
          cases e : collect argumentName args with
          | none => simp [e] at resolved
          | some found =>
            have Is : s = name ∧ found = params := by simpa [e,and_comm] using resolved
            exact ⟨cs,args,rfl,Is.1 ▸ h,Is.2 ▸ (collect_exact _ _ argument_exact _ _).mp e⟩
  · rintro ⟨cs,args,rfl,shape,selected⟩
    simp [headView,shape,(collect_exact _ _ argument_exact _ _).mpr selected]

def toHead (n : String) (p : List String) : Head := ⟨.simple n,p.map Argument.binder,true⟩

def rhsView : Tree → Option Rhs
  | .node .head cs =>
    match visible cs with
    | [.token .sigilIdentifier s] => some (.binder s)
    | [.token .identifier s] => some (.nullary s)
    | _ => none
  | _ => none

def typeView : Tree → Option Shape
  | .node .typeDecl cs =>
    match visible cs with
    | [.token .typeKw _, .token .identifier n] =>
      some ⟨n,false,.absent,true⟩
    | [.token .typeKw _, .token .identifier n, .token .equals _, rhs] =>
      (rhsView rhs).map fun body => ⟨n,true,body,true⟩
    | _ => none
  | _ => none

end Yulang.GeneralSourceRoleCstShapes293
