import Yulang.GeneralMixedFullControlMinimalRaw306
import Yulang.GeneralRebaseDepthPreEvidence286

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlModelClasses306
open GeneralMixedFullControlCode306 (Code Event code fire marker)
open GeneralMixedFullControlUnlabelled306 (classify has_label raw_exact)
open GeneralMixedFullControlMinimalRaw306 (RawBisim Reach any_raw_bisim_respects_classes)
open GeneralMixedControlRank306 (rank_successors)
open GeneralMixedControlMask306 (rank)
open GeneralMixedFullControlTrace306 (all_constructible)
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Pre Post)
open GeneralNominalCommonBridge (Assignment)

abbrev Key := Bool × Nat
def key (x : Code) : Key := (x.installed,rank x.scalars)

def successors (x : Key) : List Key :=
  (if x.1 then [] else [(true,x.2)]) ++ ((List.range x.2).map fun k => (x.1,k))

theorem scalar_preserving (x : Code) (other : Bool) (k : Nat) :
    (∃ y, GeneralMixedControlMask306.moves x.scalars y.scalars = true ∧ x.installed = y.installed ∧ key y = (other,k)) ↔
      other = x.installed ∧ k < rank x.scalars := by
  constructor
  · rintro ⟨y,step,phase,out⟩
    exact ⟨(congrArg Prod.fst out).symm.trans phase.symm,
      (rank_successors x.scalars k).mp ⟨y.scalars,step,congrArg Prod.snd out⟩⟩
  · rintro ⟨rfl,below⟩
    obtain ⟨m,h,eq⟩ := (rank_successors x.scalars k).mpr below
    exact ⟨⟨x.installed,m⟩,h,rfl,Prod.ext rfl eq⟩

theorem install_key (x : Code) (other : Bool) (k : Nat) :
    (∃ y, fire .install x y = true ∧ key y = (other,k)) ↔
      x.installed = false ∧ other = true ∧ rank x.scalars = k := by
  constructor
  · rintro ⟨y,edge,out⟩
    simp only [fire,Bool.and_eq_true_iff,Bool.not_eq_true',decide_eq_true_eq] at edge
    exact ⟨edge.1.1,(congrArg Prod.fst out).symm.trans edge.1.2,
      (congrArg rank edge.2).trans (congrArg Prod.snd out)⟩
  · rintro ⟨openNow,rfl,eq⟩
    exact ⟨⟨true,x.scalars⟩,by simp [fire,openNow],Prod.ext rfl eq⟩

theorem exact_targets (x : Code) (goal : Key) :
    (∃ y, GeneralMixedFullControlCode306.moves x y = true ∧ key y = goal) ↔
      goal ∈ successors (key x) := by
  obtain ⟨other,k⟩ := goal
  have dist : (∃ y, GeneralMixedFullControlCode306.moves x y = true ∧ key y = (other,k)) ↔
    ((∃ y, fire .install x y = true ∧ key y = (other,k)) ∨
     ∃ y, GeneralMixedControlMask306.moves x.scalars y.scalars = true ∧ x.installed = y.installed ∧ key y = (other,k)) := by
    simp only [GeneralMixedFullControlCode306.moves,Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq]
    constructor
    · rintro ⟨y,first|⟨step,phase⟩,w⟩
      · exact Or.inl ⟨y,first,w⟩
      · exact Or.inr ⟨y,step,phase,w⟩
    · rintro (⟨y,first,w⟩ | ⟨y,step,phase,w⟩)
      · exact ⟨y,Or.inl first,w⟩
      · exact ⟨y,Or.inr ⟨step,phase⟩,w⟩
  rw [dist,install_key,scalar_preserving]
  have scalar :
      (other,k) ∈ (List.range (rank x.scalars)).map (fun n => (x.installed,n)) ↔
        other = x.installed ∧ k < rank x.scalars := by
    rw [List.mem_map]
    constructor
    · rintro ⟨j,h,eq⟩
      have eqj : j = k := congrArg Prod.snd eq
      subst j
      exact ⟨(congrArg Prod.fst eq).symm,List.mem_range.mp h⟩
    · rintro ⟨rfl,lt⟩
      exact ⟨k,List.mem_range.mpr lt,rfl⟩
  rw [successors,List.mem_append]
  change (_ ∨ _) ↔ ((_ ∈ if x.installed then [] else [(true,rank x.scalars)]) ∨
    (other,k) ∈ (List.range (rank x.scalars)).map (fun n => (x.installed,n)))
  rw [scalar]
  apply or_congr ?_ Iff.rfl
  cases x.installed
  · simp only [Bool.false_eq_true,ite_false,List.mem_singleton,true_and,Prod.mk.injEq]
    exact ⟨fun q => ⟨q.1,q.2.symm⟩,fun q => ⟨q.1,q.2.symm⟩⟩
  · simp

theorem raw_targets {s : State roles} {n : Nat} (path : ActualPath initial s n) (target : Key) :
    (∃ t, Step registry root s t ∧ key (code t) = target) ↔ target ∈ successors (key (code s)) := by
  rw [← exact_targets]
  constructor
  · rintro ⟨t,step,eq⟩
    exact ⟨code t,(raw_exact path _).mpr ⟨t,step,rfl⟩,eq⟩
  · rintro ⟨c,step,eq⟩
    obtain ⟨t,whereTo,same⟩ := (raw_exact path c).mp step
    exact ⟨t,whereTo,(congrArg key same).trans eq⟩

theorem phase_iff_models {s t : State roles} {ns nt : Nat}
    (ps : ActualPath initial s ns) (pt : ActualPath initial t nt) :
    (code s).installed = (code t).installed ↔ (∀ m : Assignment, Models s m ↔ Models t m) := by
  have stageS := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) ps
  have stageT := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) pt
  rcases stageS with p|p <;> rcases stageT with q|q
  · rw [(marker ps).2.mpr p,(marker pt).2.mpr q]
    exact ⟨fun _ m => (p.anchor.models m).trans (q.anchor.models m).symm,fun _ => rfl⟩
  · rw [(marker ps).2.mpr p,(marker pt).1.mpr q]
    constructor
    · intro impossible; cases impossible
    · intro same
      have pass := (p.anchor.models _).mpr (GeneralRebaseDepthPreAnchor286.initial_models _ |>.mp small_initial)
      have bad := (GeneralRebaseDepthPostQueries286.models q smallModel).mp ((same _).mp pass)
      exact (GeneralRebaseDepthMinimal285.scalar_ne_output bad.2).elim
  · rw [(marker ps).1.mpr p,(marker pt).2.mpr q]
    constructor
    · intro impossible; cases impossible
    · intro same
      have pass := (q.anchor.models _).mpr (GeneralRebaseDepthPreAnchor286.initial_models _ |>.mp small_initial)
      have bad := (GeneralRebaseDepthPostQueries286.models p smallModel).mp ((same _).mpr pass)
      exact (GeneralRebaseDepthMinimal285.scalar_ne_output bad.2).elim
  · rw [(marker ps).1.mpr p,(marker pt).1.mpr q]
    exact ⟨fun _ m => (p.anchor.models m).trans (q.anchor.models m).symm,fun _ => rfl⟩

theorem same_shape_and_phase {x y : Code} (shape : classify x = classify y)
    (phase : x.installed = y.installed) : key x = key y := by
  rcases x with ⟨a,⟨b,c⟩⟩
  rcases y with ⟨d,⟨e,f⟩⟩
  change a = d at phase
  subst d
  cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> revert shape <;> decide

theorem necessary {rel : State roles → State roles → Prop} (b : RawBisim rel)
    (keepsModels : ∀ s t, Reach s → Reach t → rel s t → ∀ m, Models s m ↔ Models t m)
    {s t : State roles} (ps : Reach s) (pt : Reach t) (h : rel s t) :
    key (code s) = key (code t) := by
  have shape := any_raw_bisim_respects_classes b ps pt h
  have modelEq := keepsModels s t ps pt h
  obtain ⟨ns,ps⟩ := ps
  obtain ⟨nt,pt⟩ := pt
  exact same_shape_and_phase shape ((phase_iff_models ps pt).mpr modelEq)

theorem key_bisim : RawBisim (fun s t => key (code s) = key (code t)) := by
  rintro s t ⟨ns,ps⟩ ⟨nt,pt⟩ same
  constructor
  · intro u move
    have h := (raw_targets ps _).mp ⟨u,move,rfl⟩
    rw [same] at h
    obtain ⟨v,hop,eq⟩ := (raw_targets pt _).mpr h
    exact ⟨v,hop,eq.symm⟩
  · intro v move
    have h := (raw_targets pt _).mp ⟨v,move,rfl⟩
    rw [← same] at h
    obtain ⟨u,hop,eq⟩ := (raw_targets ps _).mpr h
    exact ⟨u,hop,eq⟩

theorem key_preserves_models {s t : State roles} (ps : Reach s) (pt : Reach t)
    (same : key (code s) = key (code t)) : ∀ m, Models s m ↔ Models t m := by
  obtain ⟨ns,ps⟩ := ps
  obtain ⟨nt,pt⟩ := pt
  exact (phase_iff_models ps pt).mp (congrArg Prod.fst same)

theorem each_key_reached (mode : Bool) (level : Fin 3) :
    ∃ s : State roles, Reach s ∧ key (code s) = (mode,level.val) := by
  let bits := if level.val = 0 then GeneralMixedControlLiveness306.full
    else if level.val = 1 then GeneralMixedControlLiveness306.onlyZero else GeneralMixedControlLiveness306.empty
  obtain ⟨s,n,h,eq⟩ := all_constructible ⟨mode,bits⟩
  refine ⟨s,⟨n,h⟩,?_⟩
  rw [eq]
  change (mode,rank bits) = (mode,level.val)
  refine Prod.ext rfl ?_
  change rank bits = level.val
  have cases : level.val = 0 ∨ level.val = 1 ∨ level.val = 2 := by omega
  unfold bits
  rcases cases with zero|one|two
  · rw [zero] <;> rfl
  · rw [one] <;> rfl
  · rw [two] <;> rfl

end Yulang.GeneralMixedFullControlModelClasses306
