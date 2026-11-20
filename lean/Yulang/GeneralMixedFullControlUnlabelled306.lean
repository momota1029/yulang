import Yulang.GeneralMixedFullControlStep306

namespace Yulang.GeneralMixedFullControlUnlabelled306
open GeneralMixedFullControlCode306
open GeneralMixedControlMask306 (Mask)
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)

theorem has_label (x y : Code) : moves x y = true ↔ ∃ e, fire e x y = true := by
  constructor
  · intro h
    unfold moves at h
    rcases Bool.or_eq_true_iff.mp h with installed|others
    · exact ⟨.install,installed⟩
    · obtain ⟨ab,phase⟩ := Bool.and_eq_true_iff.mp others
      obtain ⟨q,mask⟩ := (GeneralMixedControlMask306.moves_exact ..).mp ab
      exact ⟨.scalar q,Bool.and_eq_true_iff.mpr ⟨phase,mask⟩⟩
  · rintro ⟨e,edge⟩
    unfold moves
    cases e with
    | install => exact Bool.or_eq_true_iff.mpr (Or.inl edge)
    | scalar q =>
      obtain ⟨phase,mask⟩ := Bool.and_eq_true_iff.mp edge
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr
        ⟨(GeneralMixedControlMask306.moves_exact ..).mpr ⟨q,mask⟩,phase⟩))

theorem raw_exact {s : State roles} {n : Nat} (path : ActualPath initial s n) (goal : Code) :
    moves (code s) goal = true ↔ ∃ t, Step registry root s t ∧ code t = goal := by
  constructor
  · intro yes
    obtain ⟨e,edge⟩ := (has_label _ _).mp yes
    obtain ⟨t,h,tag⟩ := (GeneralMixedFullControlStep306.exact_labelled path e goal).mp edge
    exact ⟨t,action_step h,tag⟩
  · rintro ⟨t,step,eq⟩
    obtain ⟨e,action⟩ := (GeneralMixedFullControlStep306.split path).mp step
    exact (has_label _ _).mpr ⟨e,eq ▸ GeneralMixedFullControlStep306.forward path action⟩

def codes : List Code :=
  [⟨false,⟨false,false⟩⟩,⟨false,⟨true,false⟩⟩,⟨false,⟨false,true⟩⟩,⟨false,⟨true,true⟩⟩,
   ⟨true,⟨false,false⟩⟩,⟨true,⟨true,false⟩⟩,⟨true,⟨false,true⟩⟩,⟨true,⟨true,true⟩⟩]

theorem all_codes (x : Code) : x ∈ codes := by
  rcases x with ⟨a,⟨b,c⟩⟩
  cases a <;> cases b <;> cases c <;> decide

inductive ControlClass where
  | halted
  | oneLeft
  | batchable
  | separate
  | threeLeft
  deriving DecidableEq, Repr

def classify (x : Code) : ControlClass :=
  match x.installed,x.scalars.zero,x.scalars.one with
  | true,true,true => .halted
  | true,false,false => .batchable
  | true,_,_ => .oneLeft
  | false,true,true => .oneLeft
  | false,false,false => .threeLeft
  | false,_,_ => .separate

def classTargets : ControlClass → List ControlClass
  | .halted => []
  | .oneLeft => [.halted]
  | .batchable => [.halted,.oneLeft]
  | .separate => [.oneLeft]
  | .threeLeft => [.oneLeft,.batchable,.separate]

def targets (x : Code) : List Code := codes.filter (moves x)

theorem list_class_exact (x : Code) (c : ControlClass) :
    c ∈ (targets x).map classify ↔ c ∈ classTargets (classify x) := by
  rcases x with ⟨a,⟨b,d⟩⟩
  cases a <;> cases b <;> cases d <;> cases c <;> decide

theorem class_exact (x : Code) (c : ControlClass) :
    (∃ y, moves x y = true ∧ classify y = c) ↔ c ∈ classTargets (classify x) := by
  rw [← list_class_exact, List.mem_map]
  constructor
  · rintro ⟨y,step,tag⟩
    exact ⟨y,List.mem_filter.mpr ⟨all_codes y,step⟩,tag⟩
  · rintro ⟨y,listed,tag⟩
    exact ⟨y,(List.mem_filter.mp listed).2,tag⟩

theorem raw_class_exact {s : State roles} {n : Nat} (path : ActualPath initial s n) (c : ControlClass) :
    (∃ t, Step registry root s t ∧ classify (code t) = c) ↔ c ∈ classTargets (classify (code s)) := by
  rw [← class_exact]
  constructor
  · rintro ⟨t,step,tag⟩
    exact ⟨code t,(raw_exact path _).mpr ⟨t,step,rfl⟩,tag⟩
  · rintro ⟨y,edge,tag⟩
    obtain ⟨t,step,same⟩ := (raw_exact path y).mp edge
    exact ⟨t,step,(congrArg classify same).trans tag⟩

end Yulang.GeneralMixedFullControlUnlabelled306
