import Yulang.GeneralRebaseBehaviorStutters269

namespace Yulang.GeneralRebaseChangedCode269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseBehavior269 (sourceBasis code codebook code_label)
open GeneralRebaseBehaviorStutters269 (strict_or_same)
open FiniteRankBehavior269 (Code catalogue)
open GeneralRebaseStep258 (Fact)

def rank (owners : List Nat) (pool : List Output) (code : Code (List Fact)) : Nat :=
 code.label.length * ((codebook owners pool).length+1) + code.children.length

theorem children_bound (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) :
 (code registry root owners pool source).children.length ≤ (codebook owners pool).length := by
 let basis := sourceBasis registry root owners pool
 change (FiniteBehaviorClassifier269.classify basis source).children.length ≤ _
 rw [FiniteBehaviorClassifier269.classify.eq_1 basis source]
 apply Nat.le_trans (List.length_filter_le ..)
 apply (FiniteBehaviorCatalogue269.mono basis.labels _).length_le
 change (project owners pool source).remaining.length - 1 ≤ (Basis owners pool).length
 have h : (project owners pool source).remaining.length ≤ (Basis owners pool).length :=
   (project owners pool source).canonical.length_le
 omega

theorem old_or_drop (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : State roles) (step : Step registry root first last) :
 code registry root owners pool last = code registry root owners pool first ∨
 rank owners pool (code registry root owners pool last) < rank owners pool (code registry root owners pool first) := by
 by_cases same : project owners pool last = project owners pool first
 · rcases strict_or_same registry root owners pool first last (.tail .refl ⟨step,same⟩) with fixed | change
   · exact Or.inl fixed
   · right
     unfold rank
     rw [code_label,code_label,same]
     omega
 · right
   have decreases := GeneralRebaseSourceProjection264.strict_decrease owners pool step same
   have childBound := children_bound registry root owners pool last
   let cap := (codebook owners pool).length+1
   have times := Nat.mul_le_mul_right cap (Nat.succ_le_of_lt decreases)
   simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at times
   unfold rank
   rw [code_label,code_label]
   change (project owners pool last).remaining.length*cap + _ < (project owners pool first).remaining.length*cap + _
   have small : (code registry root owners pool last).children.length < cap := by
     unfold cap
     omega
   omega

/-- An existential old-edge image, with equal codes removed. This exact
relation on codes is only an overapproximation from an unknown current
representative: same-source lifting is established for Advances, not here. -/
def Changed (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (first last : Code (List Fact)) : Prop :=
 first ≠ last ∧ ∃ a b, Step registry root a b ∧ code registry root owners pool a = first ∧ code registry root owners pool b = last

theorem wellFounded (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 WellFounded (fun after before => Changed registry root owners pool before after) := by
 apply Subrelation.wf (r := InvImage Nat.lt (rank owners pool)) _ (InvImage.wf _ Nat.lt_wfRel.wf)
 rintro after before ⟨different,a,b,step,rfl,rfl⟩
 rcases old_or_drop registry root owners pool a b step with stable | progress
 · exact False.elim (different stable.symm)
 · exact progress

theorem round_or_drop (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (path : Relation.TransGen (fun after before => Step registry root before after) last first) :
 code registry root owners pool last = code registry root owners pool first ∨
 rank owners pool (code registry root owners pool last) < rank owners pool (code registry root owners pool first) := by
 induction path with
 | single step => exact old_or_drop registry root owners pool _ _ step
 | tail _ step ih =>
   rcases old_or_drop registry root owners pool _ _ step with stable | progress
   · simpa only [←stable] using ih
   · rcases ih with before | decrease
     · exact Or.inr (before.symm ▸ progress)
     · exact Or.inr (Nat.lt_trans decrease progress)

theorem eventual_rounds (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (chain : Nat → State roles)
 (rounds : ∀ n, Relation.TransGen (fun after before => Step registry root before after) (chain (n+1)) (chain n)) :
 ∃ N, ∀ n ≥ N, code registry root owners pool (chain n) = code registry root owners pool (chain N) :=
 GeneralRebaseEventualProjection265.stabilizes (fun n => code registry root owners pool (chain n))
   (rank owners pool) (fun n => round_or_drop registry root owners pool (rounds n))

end Yulang.GeneralRebaseChangedCode269
