import Yulang.GeneralRebaseCurrentStep280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseGraphBisim280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedMixedKernel234 (At Step Stable)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges models_exact aliases_exact generated_exact evidence_exact)
open GeneralRebaseCompactTrust279 (replace_twice replace_self)
open GeneralRebaseEffectSnapshot280 (ArchiveRelated SameEdges EffectRelated)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects rearchive_self archive)
open GeneralNominalCommonBridge (Assignment)

def Related (a b : State roles) : Prop :=
  ∃ edges : List (Edge roles), ∃ history : List (Effect roles),
    b = changeEffects (replaceEdges a edges) history ∧
    SameEdges a.core.erased.current.edges edges ∧ Correspond a.effects history

theorem change_eq {a b : State roles} (legacy : a.legacy = b.legacy) (plans : a.plans = b.plans) :
    b = changeEffects a b.effects := by
  cases a
  cases b
  simp only [changeEffects,State.mk.injEq]
  exact ⟨legacy.symm,plans.symm,True.intro⟩

theorem archive_trans {a b c : State roles} (one : ArchiveRelated a b) (two : ArchiveRelated b c) :
    ArchiveRelated a c := by
  refine ⟨one.legacy.trans two.legacy,one.plans.trans two.plans,?_,?_⟩
  · intro e present
    obtain ⟨mid,recorded,u⟩ := one.forward e present
    obtain ⟨last,known,v⟩ := two.forward mid recorded
    exact ⟨last,known,u.trans v⟩
  · intro last known
    obtain ⟨mid,recorded,v⟩ := two.backward last known
    obtain ⟨e,present,u⟩ := one.backward mid recorded
    exact ⟨e,present,u.trans v⟩

theorem of_archive {a b : State roles} {edges : List (Edge roles)}
    (same : SameEdges a.core.erased.current.edges edges)
    (aligned : ArchiveRelated (replaceEdges a edges) b) :
    Related a b :=
  ⟨edges,b.effects,change_eq aligned.legacy aligned.plans,same,aligned.forward,aligned.backward⟩

theorem Related.refl (a : State roles) : Related a a := by
  apply of_archive (edges := a.core.erased.current.edges) (fun _ => Iff.rfl)
  rw [replace_self]
  exact GeneralRebaseCurrentStep280.ArchiveRelated.refl a

theorem change_commute (a : State roles) (xs : List (Edge roles)) (new old : List (Effect roles)) :
    changeEffects (replaceEdges (changeEffects a old) xs) new = changeEffects (replaceEdges a xs) new := rfl

theorem Related.symm {a b : State roles} (some : Related a b) : Related b a := by
  obtain ⟨xs,ys,rfl,same,pair⟩ := some
  refine ⟨a.core.erased.current.edges,a.effects,?_,fun e => (same e).symm,pair.symm⟩
  rw [change_commute,replace_twice,replace_self,rearchive_self]

theorem models {a b : State roles} (same : Related a b) (m : Assignment) :
    Models a m ↔ Models b m := by
  obtain ⟨edges,history,rfl,_,pairs⟩ := same
  exact (models_exact a edges m).symm.trans ((archive (replaceEdges a edges) pairs).models m)

theorem generated {a b : State roles} (same : Related a b) (root focus : Occurrence roles) :
    Generated a.core.erased.current root focus ↔ Generated b.core.erased.current root focus := by
  obtain ⟨edges,archive,rfl,members,_⟩ := same
  exact (generated_exact a edges (fun e => (members e).symm) root focus).symm

theorem evidence {a b : State roles} (same : Related a b) (r : Registry) (root : Occurrence roles)
    (m : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence r a.core m root payload ↔
      GeneralNominalVersionedEvidence231.Evidence r b.core m root payload := by
  obtain ⟨edges,history,rfl,_,_⟩ := same
  exact (evidence_exact a edges r root m payload).symm

theorem at_step {a b next : State roles} (same : Related a b) (action : At r a focus next) :
    ∃ other, At r b focus other ∧ Related next other := by
  obtain ⟨edges,history,rfl,mem,pair⟩ := same
  obtain ⟨nextEdges,mid,moved,memAfter,arch⟩ := GeneralRebaseCurrentStep280.at_step mem action
  obtain ⟨other,cooked,newArchive⟩ := GeneralRebaseArchiveStep280.at_step (s := replaceEdges a edges) pair moved
  exact ⟨other,cooked,of_archive memAfter (archive_trans arch newArchive)⟩

theorem step {a b next : State roles} (same : Related a b) (action : Step r root a next) :
    ∃ other, Step r root b other ∧ Related next other := by
  obtain ⟨focus,reached,atFocus⟩ := action
  obtain ⟨other,action',aligned⟩ := at_step same atFocus
  exact ⟨other,⟨focus,(generated same root focus).mp reached,action'⟩,aligned⟩

theorem walkthrough {a b next : State roles} (same : Related a b)
    (actions : B4Target.Steps (Step r root) a next) :
    ∃ other, B4Target.Steps (Step r root) b other ∧ Related next other := by
  induction actions with
  | refl => exact ⟨b,.refl,same⟩
  | tail path action ih =>
    obtain ⟨mid,before,rel⟩ := ih
    obtain ⟨other,last,aligned⟩ := step rel action
    exact ⟨other,.tail before last,aligned⟩

theorem stable {a b : State roles} (same : Related a b) :
    Stable r a root ↔ Stable r b root := by
  constructor
  · intro terminal focus child next action
    obtain ⟨other,go,_⟩ := at_step same.symm action
    exact terminal focus ((generated same root focus).mpr child) other go
  · intro terminal focus child next action
    obtain ⟨other,go,_⟩ := at_step same action
    exact terminal focus ((generated same root focus).mp child) other go

theorem accessible {a b : State roles} (same : Related a b)
    (terminates : Acc (fun after before => Step r root before after) a) :
    Acc (fun after before => Step r root before after) b := by
  induction terminates generalizing b with
  | intro a descending ih =>
    refine Acc.intro b ?_
    intro next move
    obtain ⟨other,action,aligned⟩ := step same.symm move
    exact ih other action aligned.symm

end Yulang.GeneralRebaseGraphBisim280
