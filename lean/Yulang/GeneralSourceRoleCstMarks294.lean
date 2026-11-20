import Yulang.GeneralSourceRoleCstRustFixture293

/-! Recovery-mark enumeration on a supplied tree. The mark list is not
a list of Rust Diagnostic records. -/
namespace Yulang.GeneralSourceRoleCstMarks294
open GeneralSourceRoleCstTree293 (Tree Kind Path)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstRecovery293 (Plain TreePlain)

abbrev Mark := Path × Kind

def own (k : Kind) : List Mark :=
  if Plain k then [] else [([],k)]

mutual
def marks : Tree → List Mark
  | .token k _ => own k
  | .node k cs => own k ++ childMarks 0 cs
def childMarks : Nat → List Tree → List Mark
  | _,[] => []
  | i,x::xs => (marks x).map (fun (p,k) => (i::p,k)) ++ childMarks (i+1) xs
end

theorem own_exact (k p : Kind) (loc : Path) :
    (loc,p) ∈ own k ↔ loc = [] ∧ p = k ∧ ¬ Plain k := by
  by_cases h : Plain k <;> simp [own,h,eq_comm]

mutual
theorem marks_exact (root : Tree) (p : Path) (k : Kind) :
    (p,k) ∈ marks root ↔ ∃ t, follow p root = some t ∧ t.kind = k ∧ ¬ Plain k := by
  cases root with
  | token kind value =>
    rw [marks,own_exact]
    cases p with
    | nil =>
      constructor
      · rintro ⟨_,rfl,bad⟩
        exact ⟨_,rfl,rfl,bad⟩
      · rintro ⟨t,r,s,bad⟩
        cases Option.some.inj r
        change kind = k at s
        subst k
        exact ⟨rfl,rfl,bad⟩
    | cons n ps => simp [follow]
  | node kind cs =>
    have children := child_marks_exact cs 0 p k
    rw [marks,List.mem_append,own_exact,children]
    cases p with
    | nil =>
      constructor
      · rintro (⟨_,e,bad⟩ | ⟨i,tail,t,empty,other⟩)
        · exact ⟨_,rfl,e.symm,e.symm ▸ bad⟩
        · cases empty
      · rintro ⟨t,r,b,bad⟩
        cases Option.some.inj r
        change kind = k at b
        subst k
        exact Or.inl ⟨rfl,rfl,bad⟩
    | cons i ps =>
      constructor
      · rintro (⟨bad,_,_⟩ | ⟨j,tail,atChild,same,h⟩)
        · cases bad
        · have eq := List.cons.inj same
          rcases eq with ⟨hi,rfl⟩
          have ij : i = j := by omega
          subst i
          rcases h with ⟨read,target,addr,tag,bad⟩
          exact ⟨target,by simp [follow,read,addr],tag,bad⟩
      · rintro ⟨t,found,kind,bad⟩
        cases child : cs[i]? with
        | none => simp [follow,child] at found
        | some c =>
          exact Or.inr ⟨i,ps,c,by simp,child,t,by simpa [follow,child] using found,kind,bad⟩
theorem child_marks_exact (cs : List Tree) (base : Nat) (p : Path) (k : Kind) :
    (p,k) ∈ childMarks base cs ↔
      ∃ i tail child, p = (base+i)::tail ∧ cs[i]? = some child ∧
        ∃ t, follow tail child = some t ∧ t.kind = k ∧ ¬ Plain k := by
  cases cs with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨i,tail,c,_,read,_⟩; cases read
  | cons a as =>
    constructor
    · intro h
      rcases List.mem_append.mp h with first | rest
      · obtain ⟨⟨tail,k'⟩,mem,e⟩ := List.mem_map.mp first
        have id := Prod.mk.inj e
        rcases id with ⟨rfl,rfl⟩
        exact ⟨0,tail,a,by simp,rfl,(marks_exact ..).mp mem⟩
      · obtain ⟨i,tail,c,shape,read,below⟩ := (child_marks_exact as (base+1) p k).mp rest
        exact ⟨i+1,tail,c,by rw [shape]; congr 1 <;> omega,read,below⟩
    · rintro ⟨i,tail,c,shape,read,below⟩
      cases i with
      | zero =>
        cases Option.some.inj read
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨(tail,k),(marks_exact ..).mpr below,by simp [shape]⟩
      | succ i =>
        apply List.mem_append_right
        exact (child_marks_exact as (base+1) p k).mpr
          ⟨i,tail,c,by rw [shape]; congr 1 <;> omega,read,below⟩
end

theorem no_marks_exact (root : Tree) : marks root = [] ↔ TreePlain root := by
  constructor
  · intro empty p t located
    by_cases yes : Plain t.kind
    · exact yes
    · have hit := (marks_exact root p t.kind).mpr ⟨t,located,rfl,yes⟩
      rw [empty] at hit
      cases hit
  · intro all
    cases e : marks root with
    | nil => rfl
    | cons head tail =>
      rcases head with ⟨p,k⟩
      have hit : (p,k) ∈ marks root := by rw [e]; exact List.mem_cons_self
      obtain ⟨t,whereAt,tag,bad⟩ := (marks_exact root p k).mp hit
      exact False.elim (bad (tag ▸ all p t whereAt))

end Yulang.GeneralSourceRoleCstMarks294
