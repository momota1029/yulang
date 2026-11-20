import Yulang.GeneralSourceRoleCstSnapshot293

/-! Byte projection on the supplied lossless tree. The token weights are
UTF-8 bytes and a mixed ordinal includes trivia. -/
namespace Yulang.GeneralSourceRoleCstSpan293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstPath293 (follow)

mutual
def width : Tree → Nat
  | .token _ value => value.utf8ByteSize
  | .node _ elems => widths elems
def widths : List Tree → Nat
  | [] => 0
  | head::tail => width head + widths tail
end

def prefixWidth : Nat → List Tree → Nat
  | 0,_ => 0
  | _+1,[] => 0
  | n+1,x::xs => width x + prefixWidth n xs

structure Extent where
  low : Nat
  high : Nat
  deriving DecidableEq, Repr

def locate : Path → Tree → Nat → Option (Tree × Extent)
  | [],t,atByte => some (t,⟨atByte,atByte+width t⟩)
  | i::ps,.node _ cs,atByte => cs[i]?.bind (fun child => locate ps child (atByte + prefixWidth i cs))
  | _::_,.token _ _,_ => none

theorem prefix_child_bound {cs : List Tree} {i : Nat} {t : Tree}
    (read : cs[i]? = some t) : prefixWidth i cs + width t ≤ widths cs := by
  induction cs generalizing i with
  | nil => cases read
  | cons x xs ih =>
    cases i with
    | zero =>
      have same := Option.some.inj read
      subst x
      simp [prefixWidth,widths]
    | succ i =>
      rw [List.getElem?_cons_succ] at read
      have tail := ih read
      simp only [prefixWidth,widths]
      omega

theorem locate_tree (path : Path) (root : Tree) (start : Nat) :
    (locate path root start).map Prod.fst = follow path root := by
  induction path generalizing root start with
  | nil => rfl
  | cons n tail ih =>
    cases root with
    | token => rfl
    | node k cs =>
      cases h : cs[n]? with
      | none => simp [locate,follow,h]
      | some t => simpa [locate,follow,h] using ih t (start + prefixWidth n cs)

theorem locate_bounds {path : Path} {root t : Tree} {start : Nat} {r : Extent}
    (found : locate path root start = some (t,r)) :
    start ≤ r.low ∧ r.high = r.low + width t ∧ r.high ≤ start + width root := by
  induction path generalizing root t start r with
  | nil =>
    have e : (root, (⟨start,start+width root⟩ : Extent)) = (t,r) := Option.some.inj found
    cases e
    exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩
  | cons n tail ih =>
    cases root with
    | token => cases found
    | node k cs =>
      cases h : cs[n]? with
      | none => simp [locate,h] at found
      | some child =>
        have next : locate tail child (start+prefixWidth n cs) = some (t,r) := by
          simpa [locate,h] using found
        have here := ih next
        have step := prefix_child_bound h
        change start ≤ r.low ∧ r.high = r.low + width t ∧ r.high ≤ start + widths cs
        exact ⟨by omega,here.2.1,by omega⟩

end Yulang.GeneralSourceRoleCstSpan293
