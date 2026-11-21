import Yulang.GeneralFiniteColoredTable306

namespace Yulang.GeneralFiniteColoredEquivalence306
open GeneralFiniteColoredRounds306 (On Closed)
open GeneralFiniteColoredTable306 (compile lookup lookup_exact exact_materialized)
variable {α β : Type}
variable {edges : α → List α} {observe : α → β} {nodes : List α}

theorem equality_bisim : On edges observe nodes (fun x y => x = y) := by
  rintro x _ _ _ rfl
  exact ⟨rfl,fun a here => ⟨a,here,rfl⟩,fun a here => ⟨a,here,rfl⟩⟩

theorem flipped {rel : α → α → Prop} (bisim : On edges observe nodes rel) :
    On edges observe nodes (fun x y => rel y x) := by
  intro x xm y ym h
  have ⟨paint,forward,back⟩ := bisim y ym x xm h
  exact ⟨paint.symm,back,forward⟩

theorem composed {a b : α → α → Prop} (closed : Closed edges nodes)
    (first : On edges observe nodes a) (second : On edges observe nodes b) :
    On edges observe nodes (fun x z => ∃ y ∈ nodes, a x y ∧ b y z) := by
  rintro x xm z zm ⟨y,ym,l,r⟩
  have ⟨left,fromX,fromY⟩ := first x xm y ym l
  have ⟨right,fromMiddle,fromZ⟩ := second y ym z zm r
  refine ⟨left.trans right,?_,?_⟩
  · intro x' xe
    obtain ⟨y',ye,matchX⟩ := fromX x' xe
    obtain ⟨z',ze,matchY⟩ := fromMiddle y' ye
    exact ⟨z',ze,y',closed y ym y' ye,matchX,matchY⟩
  · intro z' ze
    obtain ⟨y',ye,matchY⟩ := fromZ z' ze
    obtain ⟨x',xe,matchX⟩ := fromY y' ye
    exact ⟨x',xe,y',closed y ym y' ye,matchX,matchY⟩

variable [DecidableEq α] [DecidableEq β]

def test (edges : α → List α) (observe : α → β) (nodes : List α) (x y : α) : Bool :=
  lookup (compile edges observe nodes) x y

theorem test_exact (closed : Closed edges nodes) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) :
    test edges observe nodes x y = true ↔ ∃ r, On edges observe nodes r ∧ r x y :=
  (lookup_exact _ _ _).trans (exact_materialized closed xm ym)

theorem refl_on (closed : Closed edges nodes) {x : α} (xm : x ∈ nodes) :
    test edges observe nodes x x = true :=
  (test_exact closed xm xm).mpr ⟨_,equality_bisim,rfl⟩

theorem symm_on (closed : Closed edges nodes) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes)
    (same : test edges observe nodes x y = true) : test edges observe nodes y x = true := by
  obtain ⟨_,bisim,rel⟩ := (test_exact closed xm ym).mp same
  exact (test_exact closed ym xm).mpr ⟨_,flipped bisim,rel⟩

theorem trans_on (closed : Closed edges nodes) {x y z : α} (xm : x ∈ nodes) (ym : y ∈ nodes) (zm : z ∈ nodes)
    (first : test edges observe nodes x y = true) (second : test edges observe nodes y z = true) :
    test edges observe nodes x z = true := by
  obtain ⟨_,before,xy⟩ := (test_exact closed xm ym).mp first
  obtain ⟨_,after,yz⟩ := (test_exact closed ym zm).mp second
  exact (test_exact closed xm zm).mpr ⟨_,composed closed before after,y,ym,xy,yz⟩

end Yulang.GeneralFiniteColoredEquivalence306
