import Yulang.GeneralRebaseBehaviorStutters269
import Yulang.GeneralRebasePartialBool268

namespace Yulang.GeneralRebaseRankOne269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Weak decrease)
open GeneralRebaseBehavior269 (code sourceBasis)
open FiniteBehaviorClassifier269 (classify)
open FiniteRankBehavior269 (Code catalogue)
open GeneralRebaseFiniteSlices268 (slices)
open GeneralRebasePartialBool268 (Answer Reflect)

theorem terminal_code (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (silent : ∀ after, ¬ Weak registry root owners pool source after) :
 code registry root owners pool source = .node (project owners pool source).remaining [] := by
 classical
 let b := sourceBasis registry root owners pool
 have h := (FiniteBehaviorClassifier269.terminal_iff b source).mpr silent
 apply GeneralRebaseBehaviorStutters269.code_ext
 · exact GeneralRebaseBehavior269.code_label registry root owners pool source
 · exact h

theorem zero_code (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (empty : (project owners pool source).remaining = []) :
 code registry root owners pool source = .node [] [] := by
 have quiet : ∀ after, ¬ Weak registry root owners pool source after := by
   intro yet step
   have decrease := decrease step
   rw [empty] at decrease
   exact Nat.not_lt_zero _ decrease
 rw [terminal_code registry root owners pool source quiet,empty]

def oneCode (basis current : List Fact) (hasAdvance : Bool) : Code (List Fact) :=
 .node current ((catalogue (slices basis) 0).filter fun c => hasAdvance && c.label.isEmpty)

/-- Compute the complete code on the rank-zero/one fragment. A rank-one
positive answer needs only one actual weak witness, since all weak targets
have the same (terminal, empty label) continuation code. A negative needs
independent no-weak-step evidence, not an incomplete search. -/
def tryCode (basis current : List Fact) (hasAdvance : Answer) : Option (Code (List Fact)) :=
 if current.isEmpty then some (.node [] []) else
 if current.length = 1 then hasAdvance.map (oneCode basis current) else none

theorem rankOne_correct (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (rank : (project owners pool source).remaining.length = 1)
 (bit : Bool) (cert : Reflect (∃ after, Weak registry root owners pool source after) (some bit)) :
 code registry root owners pool source =
 oneCode (Basis owners pool) (project owners pool source).remaining bit := by
 classical
 let b := sourceBasis registry root owners pool
 change classify b source = _
 rw [classify.eq_1 b source]
 have bRank : b.rank source - 1 = 0 := by change (project owners pool source).remaining.length - 1 = 0; omega
 rw [bRank]
 apply congrArg (Code.node (project owners pool source).remaining)
 apply List.filter_congr
 intro c listed
 obtain ⟨label,_inside,rfl⟩ := List.mem_map.mp listed
 simp only [Code.label]
 have targets (after : State roles) (step : Weak registry root owners pool source after) :
     classify b after = .node [] [] := by
   apply zero_code
   apply List.length_eq_zero_iff.mp
   have smaller := decrease step
   omega
 cases bit with
 | false =>
   simp only [Bool.false_and,decide_eq_false_iff_not]
   rintro ⟨after,_⟩
   exact cert ⟨after.val,after.property⟩
 | true =>
   rw [Bool.eq_iff_iff]
   simp only [Bool.true_and,List.isEmpty_iff,decide_eq_true_eq]
   constructor
   · intro existsStep
     obtain ⟨after,eq⟩ := existsStep
     have equal : (.node [] [] : Code (List Fact)) = .node label [] :=
       (targets after.val after.property).symm.trans eq
     cases equal
     rfl
   · intro empty
     subst label
     obtain ⟨after,step⟩ := cert
     exact ⟨⟨after,step⟩,targets after step⟩

theorem sound (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (source : State roles) (hasAdvance : Answer)
 (cert : Reflect (∃ after, Weak registry root owners pool source after) hasAdvance)
 (found : tryCode (Basis owners pool) (project owners pool source).remaining hasAdvance = some c) :
 code registry root owners pool source = c := by
 unfold tryCode at found
 split at found
 · rename_i emp
   exact (zero_code registry root owners pool source (List.isEmpty_iff.mp emp)).trans (Option.some.inj found)
 · split at found
   · rename_i one
     cases hasAdvance with
     | none => cases found
     | some bit =>
       exact (rankOne_correct registry root owners pool source one bit cert).trans (Option.some.inj found)
   · cases found

end Yulang.GeneralRebaseRankOne269
