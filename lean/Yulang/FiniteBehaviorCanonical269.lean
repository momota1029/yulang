import Yulang.FiniteBehaviorClassifier269

namespace Yulang.FiniteBehaviorCanonical269
open FiniteRankBehavior269 (Code catalogue)
open FiniteBehaviorClassifier269 (Basis classify classifier_label transfer_step)

structure Bisimulation (basis : Basis Source Label) (related : Source → Source → Prop) : Prop where
 labels : ∀ a b, related a b → basis.observe a = basis.observe b
 ranks : ∀ a b, related a b → basis.rank a = basis.rank b
 forward : ∀ a b x, related a b → basis.move a x → ∃ y, basis.move b y ∧ related x y
 backward : ∀ a b y, related a b → basis.move b y → ∃ x, basis.move a x ∧ related x y

theorem equal_is_bisimulation (basis : Basis Source Label)
 (fromLabel : ∀ a b, basis.observe a = basis.observe b → basis.rank a = basis.rank b) :
 Bisimulation basis (fun a b => classify basis a = classify basis b) := by
 have inherited : ∀ a b, classify basis a = classify basis b → basis.observe a = basis.observe b := by
   intro a b same
   rw [←classifier_label basis a,←classifier_label basis b,same]
 refine ⟨inherited,fun a b h => fromLabel a b (inherited a b h),?_,?_⟩
 · intro a b x equal advance
   exact transfer_step basis equal advance
 · intro a b y equal advance
   obtain ⟨x,move,eq⟩ := transfer_step basis equal.symm advance
   exact ⟨x,move,eq.symm⟩

/-- Any rank- and label-preserving bisimulation is contained in equality of
the finite classifier. The proof compares canonical finite child lists,
not arbitrarily ordered finite sets and not one-step observations. -/
theorem maximal (basis : Basis Source Label) (related : Source → Source → Prop)
 (bisim : Bisimulation basis related) (a b : Source) (same : related a b) :
 classify basis a = classify basis b := by
 classical
 generalize hRank : basis.rank a = rank
 induction rank using Nat.strongRecOn generalizing a b with
 | ind rank ih =>
   have toRank : basis.rank b = rank := (bisim.ranks a b same).symm.trans hRank
   rw [classify.eq_1 basis a,classify.eq_1 basis b,bisim.labels a b same,hRank,toRank]
   apply congrArg (Code.node (basis.observe b))
   apply List.filter_congr
   intro code _
   have propeq : (∃ successor : {s // basis.move a s},classify basis successor.val = code) =
                 (∃ successor : {s // basis.move b s},classify basis successor.val = code) := by
     apply propext
     constructor
     · rintro ⟨next,eq⟩
       obtain ⟨companion,advance,pair⟩ := bisim.forward a b next.val same next.property
       have small := basis.decreases a next.val next.property
       rw [hRank] at small
       exact ⟨⟨companion,advance⟩,(ih _ small next.val companion pair rfl).symm.trans eq⟩
     · rintro ⟨next,eq⟩
       obtain ⟨companion,advance,pair⟩ := bisim.backward a b next.val same next.property
       have small := basis.decreases a companion advance
       rw [hRank] at small
       exact ⟨⟨companion,advance⟩,(ih _ small companion next.val pair rfl).trans eq⟩
   simp only [propeq]

theorem characterizes (basis : Basis Source Label)
 (fromLabel : ∀ a b, basis.observe a = basis.observe b → basis.rank a = basis.rank b)
 (a b : Source) :
 classify basis a = classify basis b ↔
 ∃ related : Source → Source → Prop, Bisimulation basis related ∧ related a b :=
 ⟨fun h => ⟨_,equal_is_bisimulation basis fromLabel,h⟩,fun ⟨_,valid,source⟩ => maximal basis _ valid a b source⟩

end Yulang.FiniteBehaviorCanonical269
