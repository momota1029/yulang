import Yulang.GeneralFiniteColoredExact306

namespace Yulang.GeneralFiniteColoredTable306
open GeneralFiniteColoredRounds306 (Closed On paint rounds expand)
open GeneralFiniteColoredScore306 (pairs mem_pairs)
open GeneralFiniteColoredExact306 (limit analyze exact_checked)
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def lookup (table : List (α × α)) (x y : α) : Bool :=
  table.any (fun p => decide ((x,y) = p))

theorem lookup_exact (table : List (α × α)) (x y : α) :
    lookup table x y = true ↔ (x,y) ∈ table := by
  unfold lookup
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p,member,eq⟩
    exact (of_decide_eq_true eq).symm ▸ member
  · intro yes
    exact ⟨_,yes,decide_eq_true rfl⟩

def advance (edges : α → List α) (observe : α → β) (nodes : List α) (old : List (α × α)) : List (α × α) :=
  (pairs nodes).filter fun p => paint observe p.1 p.2 &&
    GeneralFiniteBisimRefinement306.refine edges (lookup old) p.1 p.2

def table (edges : α → List α) (observe : α → β) (nodes : List α) : Nat → List (α × α)
  | 0 => (pairs nodes).filter fun p => paint observe p.1 p.2
  | n+1 => advance edges observe nodes (table edges observe nodes n)

theorem materialized {edges : α → List α} {observe : α → β} {nodes : List α}
    (closed : Closed edges nodes) (n : Nat) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) :
    lookup (table edges observe nodes n) x y = rounds edges observe n x y := by
  induction n generalizing x y with
  | zero =>
    apply Bool.eq_iff_iff.mpr
    rw [lookup_exact]
    change (x,y) ∈ ((pairs nodes).filter _) ↔ _
    rw [List.mem_filter]
    exact ⟨And.right,fun yes => ⟨(mem_pairs nodes x y).mpr ⟨xm,ym⟩,yes⟩⟩
  | succ n ih =>
    apply Bool.eq_iff_iff.mpr
    rw [lookup_exact]
    change (x,y) ∈ ((pairs nodes).filter _) ↔ _
    rw [List.mem_filter]
    have both : (x,y) ∈ pairs nodes := (mem_pairs nodes x y).mpr ⟨xm,ym⟩
    simp only [paint,GeneralFiniteBisimRefinement306.refine,Bool.and_eq_true_iff,
      decide_eq_true_eq,List.all_eq_true,List.any_eq_true,true_and,both]
    rw [expand]
    constructor
    · rintro ⟨color,forward,back⟩
      refine ⟨color,?_,?_⟩
      · intro a inFirst
        obtain ⟨b,inLast,h⟩ := forward a inFirst
        exact ⟨b,inLast,ih (closed x xm a inFirst) (closed y ym b inLast) ▸ h⟩
      · intro b inLast
        obtain ⟨a,inFirst,h⟩ := back b inLast
        exact ⟨a,inFirst,ih (closed x xm a inFirst) (closed y ym b inLast) ▸ h⟩
    · rintro ⟨color,forward,back⟩
      refine ⟨color,?_,?_⟩
      · intro a inFirst
        obtain ⟨b,inLast,h⟩ := forward a inFirst
        exact ⟨b,inLast,(ih (closed x xm a inFirst) (closed y ym b inLast)).symm ▸ h⟩
      · intro b inLast
        obtain ⟨a,inFirst,h⟩ := back b inLast
        exact ⟨a,inFirst,(ih (closed x xm a inFirst) (closed y ym b inLast)).symm ▸ h⟩

def compile (edges : α → List α) (observe : α → β) (nodes : List α) : List (α × α) :=
  table edges observe nodes (limit nodes)

theorem exact_materialized {edges : α → List α} {observe : α → β} {nodes : List α}
    (closed : Closed edges nodes) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) :
    (x,y) ∈ compile edges observe nodes ↔ ∃ rel, On edges observe nodes rel ∧ rel x y := by
  rw [← lookup_exact,compile,materialized closed (limit nodes) xm ym]
  exact exact_checked closed xm ym

end Yulang.GeneralFiniteColoredTable306
