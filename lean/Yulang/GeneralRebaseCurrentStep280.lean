import Yulang.GeneralRebaseArchiveStep280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCurrentStep280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedMixedKernel234 (Administrative At Step)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges models_exact aliases_exact generated_exact committed_exact)
open GeneralRebaseCompactObservationGuard279 (refreshForward revisionForward certificate improves)
open GeneralRebaseCompactInstallGuard279 (reframe enabled_iff)
open GeneralRebaseEffectSnapshot280 (ArchiveRelated EffectRelated SameEdges coreAt retag)
open GeneralRebaseArchiveTrust280 (archive changeEffects Correspond same_inputs_mono)

variable {roles : Roles.RoleDecls} {s next : State roles} {ys : List (Edge roles)}

theorem equal_effect {a b : Effect roles} (registry : a.registry = b.registry)
    (snapshot : a.snapshot = b.snapshot) (plan : a.plan = b.plan) : a = b := by
  cases a
  cases b
  simp only [Effect.mk.injEq]
  exact ⟨registry,snapshot,plan⟩

theorem reframed_related {e : Effect roles} (snapshot : e.snapshot = s.core)
    (members : SameEdges s.core.erased.current.edges ys) :
    EffectRelated e (reframe e snapshot ys) := by
  refine ⟨ys,equal_effect rfl ?_ rfl,?_⟩
  · change coreAt s.core ys = coreAt e.snapshot ys
    rw [snapshot]
  · rw [snapshot]
    exact members

theorem Correspond.refl (effects : List (Effect roles)) : Correspond effects effects :=
  ⟨fun e h => ⟨e,h,EffectRelated.refl e⟩,fun e h => ⟨e,h,EffectRelated.refl e⟩⟩

theorem ArchiveRelated.refl (state : State roles) : ArchiveRelated state state :=
  ⟨rfl,rfl,(Correspond.refl state.effects).1,(Correspond.refl state.effects).2⟩

theorem admin (action : Administrative s focus next) :
    Administrative (replaceEdges s ys) focus (replaceEdges next ys) := by
  cases action with
  | enqueue linked absent =>
    exact .enqueue _ linked absent
  | refresh context cert source one two three =>
    exact .refresh _ context (refreshForward cert) source one two three
  | equate first last a b equal fresh =>
    exact .equate _ first last a b (fun m h => equal m ((models_exact s ys m).mp h)) fresh
  | reobserve rev cert increase =>
    exact .reobserve _ (revisionForward (new := ys) rev) (certificate cert) (improves increase)

theorem admin_membership (action : Administrative s focus next)
    (same : SameEdges s.core.erased.current.edges ys) :
    SameEdges next.core.erased.current.edges ys := by
  cases action <;> exact same

theorem at_step (same : SameEdges s.core.erased.current.edges ys) (action : At r s focus next) :
    ∃ newEdges target, At r (replaceEdges s ys) focus target ∧
      SameEdges next.core.erased.current.edges newEdges ∧ ArchiveRelated (replaceEdges next newEdges) target := by
  cases action with
  | administrative act =>
    exact ⟨ys,_,.administrative (admin act),admin_membership act same,ArchiveRelated.refl _⟩
  | refresh _ context cert source one two three =>
    exact ⟨ys,_,.refresh _ context (refreshForward cert) source one two three,same,ArchiveRelated.refl _⟩
  | merge first last a b equal novel =>
    exact ⟨ys,_,.merge first last a b
      (same_inputs_mono (fun m h => (models_exact s ys m).mp h) equal)
      ((not_congr (aliases_exact s ys _ _)).mpr novel),same,ArchiveRelated.refl _⟩
  | install effect enabled fresh =>
    let nextEdges := ys ++ GeneralNominalVersionedChildren232.edges effect.plan
    let newEffect := reframe effect enabled.snapshot_eq ys
    refine ⟨nextEdges,_,.install newEffect ((enabled_iff enabled.snapshot_eq).mpr enabled)
      ((not_congr (committed_exact s ys (fun e => (same e).symm) effect.plan)).mpr fresh),?_,?_⟩
    · intro e
      change (e ∈ s.core.erased.current.edges ++ _ ↔ e ∈ ys ++ _)
      simp only [List.mem_append,same e]
    · have pairs := Correspond.cons (Correspond.refl s.effects) (reframed_related enabled.snapshot_eq same)
      exact ⟨rfl,rfl,pairs.1,pairs.2⟩

end Yulang.GeneralRebaseCurrentStep280
