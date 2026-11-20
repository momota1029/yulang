import Yulang.GeneralSourceRoleCstShapes293

/-! Classify a direct statement without a descendant search. The emitted path
points to the ordinary declaration node under the direct Statement wrapper. -/
namespace Yulang.GeneralSourceRoleCstBody293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleSyntaxBoundary292 (Shape)
open GeneralSourceRoleExport292 (collect collect_exact Aligned)

def classify : Tree → Option Child
  | .node .typeDecl cs => (typeView (.node .typeDecl cs)).map Child.typeDecl
  | .node .binding cs => if cleanList cs then some .other else none
  | _ => none

inductive Classification : Tree → Child → Prop
  | associated (cs : List Tree) (out : Shape) :
      typeView (.node .typeDecl cs) = some out →
      Classification (.node .typeDecl cs) (.typeDecl out)
  | binding (cs : List Tree) : cleanList cs = true →
      Classification (.node .binding cs) .other

theorem classify_exact (tree : Tree) (child : Child) :
    classify tree = some child ↔ Classification tree child := by
  constructor
  · intro h
    cases tree with
    | token => cases h
    | node k cs =>
      cases k <;> try cases h
      · cases e : typeView (.node .typeDecl cs) with
        | none => simp [classify,e] at h
        | some x =>
          have eq : Child.typeDecl x = child := by simpa [classify,e] using h
          subst child
          exact .associated cs x e
      · by_cases ok : cleanList cs = true
        · have eq : Child.other = child := by simpa [classify,ok] using h
          subst child
          exact .binding cs ok
        · simp [classify,ok] at h
  · intro h
    cases h with
    | associated cs x e => simp [classify,e]
    | binding cs ok => simp [classify,ok]

def statement (base : Path) (tree : Tree) : Option (Path × Child) :=
  match tree with
  | .node .statement cs =>
    match significant cs with
    | [(i,inner)] => (classify inner).map fun child => (base ++ [i],child)
    | _ => none
  | _ => none

def IsStatement (base : Path) (tree : Tree) (r : Path × Child) : Prop :=
  ∃ cs i inner, tree = .node .statement cs ∧ significant cs = [(i,inner)] ∧
    r.1 = base ++ [i] ∧ Classification inner r.2

theorem statement_exact (base : Path) (tree : Tree) (r : Path × Child) :
    statement base tree = some r ↔ IsStatement base tree r := by
  constructor
  · intro h
    cases tree with
    | token => cases h
    | node k cs =>
      cases k <;> try cases h
      cases e : significant cs with
      | nil => simp [statement,e] at h
      | cons fst tl =>
        cases tl with
        | cons extra tail => simp [statement,e] at h
        | nil =>
          obtain ⟨i,inner⟩ := fst
          cases c : classify inner with
          | none => simp [statement,e,c] at h
          | some val =>
            have eq : (base ++ [i],val) = r := by simpa [statement,e,c] using h
            subst r
            exact ⟨cs,i,inner,rfl,e,rfl,(classify_exact ..).mp c⟩
  · rintro ⟨cs,i,inner,rfl,shape,atChild,kind⟩
    rcases r with ⟨path,c⟩
    change path = base ++ [i] at atChild
    subst path
    simp [statement,shape,(classify_exact ..).mpr kind]

def members (base : Path) (tree : Tree) : Option (List (Path × Child)) :=
  match tree with
  | .node .indented cs => collect (fun p => statement (base ++ [p.1]) p.2) (significant cs)
  | _ => none

theorem members_exact (base : Path) (tree : Tree) (results : List (Path × Child)) :
    members base tree = some results ↔
      ∃ cs, tree = .node .indented cs ∧
        Aligned (fun p => IsStatement (base ++ [p.1]) p.2) (significant cs) results := by
  constructor
  · intro h
    cases tree with
    | token => cases h
    | node k cs =>
      cases k <;> try cases h
      exact ⟨cs,rfl,(collect_exact _ _ (fun (p : Nat × Tree) => statement_exact (base ++ [p.1]) p.2) _ _).mp h⟩
  · rintro ⟨cs,rfl,h⟩
    exact (collect_exact _ _ (fun (p : Nat × Tree) => statement_exact (base ++ [p.1]) p.2) _ _).mpr h

end Yulang.GeneralSourceRoleCstBody293
