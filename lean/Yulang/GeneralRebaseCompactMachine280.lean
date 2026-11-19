import Yulang.GeneralRebaseGraphBisim280
import Yulang.GeneralRebaseEdgeLedger279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCompactMachine280
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralRebaseGraphBisim280 (Related change_commute)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges)
open GeneralRebaseCompactTrust279 (replace_twice)
open GeneralRebaseEffectSnapshot280 (SameEdges EffectRelated retag retag_twice)
open GeneralRebaseEdgeLedger279 (normalize normalize_members normalize_nodup normalize_idempotent)

theorem correspond_trans {first mid last : List (Effect roles)}
    (one : Correspond first mid) (two : Correspond mid last) : Correspond first last := by
  constructor
  · intro e found
    obtain ⟨m,member,left⟩ := one.1 e found
    obtain ⟨f,present,right⟩ := two.1 m member
    exact ⟨f,present,left.trans right⟩
  · intro f found
    obtain ⟨m,member,right⟩ := two.2 f found
    obtain ⟨e,present,left⟩ := one.2 m member
    exact ⟨e,present,left.trans right⟩

theorem related_trans {a b c : State roles} (first : Related a b) (last : Related b c) : Related a c := by
  obtain ⟨xs,ys,rfl,firstEdges,firstHistory⟩ := first
  obtain ⟨u,v,rfl,lastEdges,lastHistory⟩ := last
  refine ⟨u,v,?_,fun e => (firstEdges e).trans (lastEdges e),correspond_trans firstHistory lastHistory⟩
  rw [change_commute,replace_twice]

def compactEffect (old : Effect roles) : Effect roles :=
  retag old (normalize old.snapshot.erased.current.edges)

def compact (old : State roles) : State roles :=
  changeEffects (replaceEdges old (normalize old.core.erased.current.edges)) (old.effects.map compactEffect)

theorem compact_effect_related (e : Effect roles) : EffectRelated e (compactEffect e) :=
  ⟨_,rfl,fun edge => (normalize_members _ edge).symm⟩

theorem compact_related (s : State roles) : Related s (compact s) := by
  refine ⟨_,_,rfl,fun e => (normalize_members _ e).symm,?_,?_⟩
  · intro e stored
    exact ⟨compactEffect e,List.mem_map.mpr ⟨e,stored,rfl⟩,compact_effect_related e⟩
  · intro f stored
    obtain ⟨e,recorded,rfl⟩ := List.mem_map.mp stored
    exact ⟨e,recorded,compact_effect_related e⟩

theorem current_unique (s : State roles) : (compact s).core.erased.current.edges.Nodup :=
  normalize_nodup _

theorem stored_unique (s : State roles) (e : Effect roles) (mem : e ∈ (compact s).effects) :
    e.snapshot.erased.current.edges.Nodup := by
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp mem
  exact normalize_nodup _

theorem compact_effect_twice (e : Effect roles) : compactEffect (compactEffect e) = compactEffect e := by
  change retag (retag e (normalize e.snapshot.erased.current.edges))
    (normalize (normalize e.snapshot.erased.current.edges)) = _
  rw [normalize_idempotent,retag_twice]
  rfl

theorem compact_twice (s : State roles) : compact (compact s) = compact s := by
  unfold compact
  change changeEffects
    (replaceEdges (changeEffects (replaceEdges s (normalize s.core.erased.current.edges)) (s.effects.map compactEffect))
      (normalize (normalize s.core.erased.current.edges))) ((s.effects.map compactEffect).map compactEffect) = _
  rw [normalize_idempotent,change_commute,replace_twice,List.map_map]
  simp only [Function.comp_def,compact_effect_twice]

def CompactStep (r : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ raw, Step r root before raw ∧ after = compact raw

theorem reduced_targets (go : CompactStep r root before after) :
    compact after = after := by
  obtain ⟨raw,_,rfl⟩ := go
  exact compact_twice raw

theorem lift {a b next : State roles} (rel : Related a b) (move : Step r root a next) :
    ∃ other, CompactStep r root b other ∧ Related next other := by
  obtain ⟨raw,step,aligned⟩ := GeneralRebaseGraphBisim280.step rel move
  exact ⟨compact raw,⟨raw,step,rfl⟩,related_trans aligned (compact_related raw)⟩

theorem lower {a b next : State roles} (rel : Related a b) (move : CompactStep r root b next) :
    ∃ other, Step r root a other ∧ Related other next := by
  obtain ⟨raw,step,rfl⟩ := move
  obtain ⟨other,valid,aligned⟩ := GeneralRebaseGraphBisim280.step rel.symm step
  exact ⟨other,valid,related_trans aligned.symm (compact_related raw)⟩

theorem lift_path {a b next : State roles} (rel : Related a b)
    (walk : B4Target.Steps (Step r root) a next) :
    ∃ other, B4Target.Steps (CompactStep r root) b other ∧ Related next other := by
  induction walk with
  | refl => exact ⟨b,.refl,rel⟩
  | tail path action ih =>
    obtain ⟨middle,trace,same⟩ := ih
    obtain ⟨out,move,aligned⟩ := lift same action
    exact ⟨out,.tail trace move,aligned⟩

theorem lower_path {a b next : State roles} (rel : Related a b)
    (walk : B4Target.Steps (CompactStep r root) b next) :
    ∃ other, B4Target.Steps (Step r root) a other ∧ Related other next := by
  induction walk with
  | refl => exact ⟨a,.refl,rel⟩
  | tail path action ih =>
    obtain ⟨middle,trace,same⟩ := ih
    obtain ⟨out,move,aligned⟩ := lower same action
    exact ⟨out,.tail trace move,aligned⟩

theorem terminal_iff {a b : State roles} (rel : Related a b) :
    Stable r a root ↔ ¬ ∃ out, CompactStep r root b out := by
  rw [GeneralRebaseCompactAvailability279.stable_iff_not_step]
  apply not_congr
  constructor
  · rintro ⟨out,step⟩
    obtain ⟨target,moved,_⟩ := lift rel step
    exact ⟨target,moved⟩
  · rintro ⟨out,step⟩
    obtain ⟨target,moved,_⟩ := lower rel step
    exact ⟨target,moved⟩

theorem acc_forward {a b : State roles} (rel : Related a b)
    (proved : Acc (fun after before => Step r root before after) a) :
    Acc (fun after before => CompactStep r root before after) b := by
  induction proved generalizing b with
  | intro a _ ih =>
    refine Acc.intro b ?_
    intro next move
    obtain ⟨out,valid,aligned⟩ := lower rel move
    exact ih out valid aligned

theorem acc_backward {a b : State roles} (rel : Related a b)
    (proved : Acc (fun after before => CompactStep r root before after) b) :
    Acc (fun after before => Step r root before after) a := by
  induction proved generalizing a with
  | intro b _ ih =>
    refine Acc.intro a ?_
    intro next move
    obtain ⟨out,valid,aligned⟩ := lift rel move
    exact ih out valid aligned

theorem acc_exact (s : State roles) (r : Registry) (root : Occurrence roles) :
    Acc (fun after before => Step r root before after) s ↔
      Acc (fun after before => CompactStep r root before after) (compact s) :=
  ⟨acc_forward (compact_related s),acc_backward (compact_related s)⟩

end Yulang.GeneralRebaseCompactMachine280
