import Yulang.GeneralRebaseRawObserver297
import Yulang.GeneralRebaseDepthCompiler297

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseRawDepthReplay297
open GeneralDictionaryOutputDepth252 (roles sourceRegistry registry declaration root initial plan packet model snapshot reachable)
open GeneralDictionaryOutputDepthInstall252 (effect installed smallModel small_source installable)
open GeneralRebaseSignedDepth297 (checked pool)
open GeneralRebaseDepthCompiler297 (entries)
open GeneralRebaseOutputDepthSuccessor271 (owner output projected_install initial_view)
open GeneralRebaseSourceWitnessProgram297 (Checks headTest registeredPairs questions Observed)
open GeneralRebasePriorWitness297 (values)
open GeneralRebaseRawObserver297 (ExactSafety observe)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSignedModels297 (Sign)
open GeneralNominalVersionedPlans231 (private_models_iff)
open CommonNominalFullCarrier (subtype_refl)

def checks : Checks roles :=
  ⟨fun _ _ => true,fun _ => true,fun _ a => GeneralRebaseSignedDepth297.nested a,fun _ _ => true⟩

def safety (_ : GeneralSourceDictionaries.Occurrence roles) : Bool := true

theorem safe_exact : ExactSafety sourceRegistry initial root safety := by
  intro f generated
  have only : GeneralRebaseExecutableGenerated267.discover initial.core.erased.current root = [root] := by
    have length : (GeneralRebaseExecutableGenerated267.discover initial.core.erased.current root).length = 1 := by decide +kernel
    have head := (GeneralRebaseExecutableGenerated267.discover_exact ..).mpr
      (GeneralNominalSaturationState.Generated.root (root := root) (state := initial.core.erased.current))
    generalize eq : GeneralRebaseExecutableGenerated267.discover initial.core.erased.current root = xs at length head ⊢
    cases xs with
    | nil => cases length
    | cons x xs =>
      cases xs with
      | nil => exact congrArg (fun a => [a]) (List.mem_singleton.mp head).symm
      | cons y ys => simp at length
  have mem := (GeneralRebaseExecutableGenerated267.discover_exact ..).mpr generated
  rw [only] at mem
  cases List.mem_singleton.mp mem
  exact ⟨fun _ => installable.safe,fun _ => rfl⟩

theorem small_head : headTest plan smallModel := by
  change GeneralNominalVersionedPlans231.HeadModels packet smallModel
  constructor
  · apply (private_models_iff packet smallModel).mpr
    refine ⟨small_source,?_,?_,?_⟩
    · rw [GeneralDictionaryOutputDepth252.bindings_exact]
      intro a am b bm _
      cases List.mem_singleton.mp am
      cases List.mem_singleton.mp bm
      exact subtype_refl _
    · rw [GeneralDictionaryOutputDepth252.bindings_exact]
      exact PresenceNormalForm.all_nil _ _
    · change PresenceNormalForm.All CommonNominalFullCarrier.model smallModel
        (GeneralNominalRecursiveInspection.selfChecks snapshot (GeneralNominalRecursiveCandidates.report
          GeneralDictionaryOutputDepth252.context declaration [(2,2)]))
      rw [GeneralDictionaryOutputDepth252.report_exact]
      change PresenceNormalForm.All CommonNominalFullCarrier.model smallModel
        [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2)]
      intro atom present
      rcases List.mem_cons.mp present with rfl | rest
      · exact subtype_refl _
      · cases List.mem_singleton.mp rest
        exact subtype_refl _
  · change GeneralNominalRecursiveInspection.ProjectionModels snapshot
      (GeneralNominalRecursiveCandidates.report GeneralDictionaryOutputDepth252.context declaration [(2,2)]) smallModel
    rw [GeneralDictionaryOutputDepth252.report_exact]
    refine ⟨(by intro _ h; cases h),(by intro _ h; cases h),?_,?_⟩
    · intro first one last two _ ref located
      cases List.mem_singleton.mp one
      cases located
    · intro first one last two _ a b located
      cases List.mem_singleton.mp one
      cases located

theorem observed :
    Observed initial (values pool) (GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked) checks := by
  rw [entries]
  refine ⟨?_,GeneralRebaseDepthCompiler297.all_models_checked,?_⟩
  · intro p inPlan a listed
    cases List.mem_singleton.mp inPlan
    have found : a = model ∨ a = smallModel := by
      change a ∈ [model,smallModel] at listed
      simpa using listed
    rcases found with rfl | rfl
    · exact ⟨fun _ => GeneralDictionaryOutputDepth252.head_model,fun _ => rfl⟩
    · exact ⟨fun _ => small_head,fun _ => rfl⟩
  · intro pair listed a _
    obtain ⟨l,r⟩ := pair
    obtain ⟨la,ra⟩ := (GeneralRebaseSourceWitnessProgram297.pairs_exact initial l r).mp listed
    change l ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at la
    change r ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at ra
    cases List.mem_singleton.mp la
    cases List.mem_singleton.mp ra
    refine ⟨fun _ => ?_,fun _ => rfl⟩
    change ∀ c ∈ [(2,2)], CommonNominalFullCarrier.Equivalent (a c.1).1 (a c.2).1
    intro pair member
    cases List.mem_singleton.mp member
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem program_covers : GeneralRebaseFiniteWitnessTable297.Covers
    (GeneralRebaseSourceWitnessProgram297.Holds initial)
      (questions sourceRegistry initial root checked) (values pool) := by
  intro q listed h
  rcases q with p | ⟨p,sign⟩ | pair
  · unfold questions at listed
    rw [entries] at listed
    have equal : p = plan := by
      rcases List.mem_append.mp listed with pos|other
      · rcases List.mem_append.mp pos with isHead|isInstall
        · obtain ⟨p',inPlan,eq⟩ := List.mem_map.mp isHead
          exact (GeneralRebaseSourceWitnessProgram297.Question.head.inj eq).symm.trans
            (List.mem_singleton.mp inPlan)
        · obtain ⟨q',_,wrong⟩ := List.mem_map.mp isInstall
          cases wrong
      · obtain ⟨pair',_,wrong⟩ := List.mem_map.mp other
        cases wrong
    subst p
    exact ⟨model,List.mem_map_of_mem (List.mem_cons_self ..),GeneralDictionaryOutputDepth252.head_model⟩
  · unfold questions at listed
    rw [entries] at listed
    rcases List.mem_append.mp listed with pos|other
    · rcases List.mem_append.mp pos with isHead|isInstall
      · obtain ⟨q',_,wrong⟩ := List.mem_map.mp isHead
        cases wrong
      · obtain ⟨⟨p',sign'⟩,found,eq⟩ := List.mem_map.mp isInstall
        cases eq
        exact GeneralRebaseSignedDepth297.pool_covers (p',sign') found h
    · obtain ⟨pair',_,wrong⟩ := List.mem_map.mp other
      cases wrong
  · unfold questions at listed
    rcases List.mem_append.mp listed with pos|other
    · rcases List.mem_append.mp pos with isHead|isInstall
      · obtain ⟨q',_,wrong⟩ := List.mem_map.mp isHead
        cases wrong
      · obtain ⟨q',_,wrong⟩ := List.mem_map.mp isInstall
        cases wrong
    · obtain ⟨pair',found,eq⟩ := List.mem_map.mp other
      cases eq
      obtain ⟨a,old,no⟩ := h
      obtain ⟨first,last⟩ := pair
      obtain ⟨la,ra⟩ := (GeneralRebaseSourceWitnessProgram297.pairs_exact initial first last).mp found
      change first ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at la
      change last ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at ra
      cases List.mem_singleton.mp la
      cases List.mem_singleton.mp ra
      apply False.elim
      apply no
      change ∀ p ∈ [(2,2)], CommonNominalFullCarrier.Equivalent (a p.1).1 (a p.2).1
      intro p member
      cases List.mem_singleton.mp member
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem metadata : GeneralNominalRecursiveCandidates.Metadata registry initial.core.erased.current.context :=
  GeneralDictionaryOutputDepth252.metadata

theorem exact_raw_projection (target : GeneralRebaseStep258.State
    (GeneralRebaseCompression266.Basis [owner] [output])) :
    GeneralRebaseStep258.Step (observe sourceRegistry initial root checked (values pool) checks safety [owner] [output])
      (GeneralRebaseLiveProjection264.project [owner] [output] initial) target ↔
    ∃ after, (Boundary roles).Step sourceRegistry root initial after ∧
      GeneralRebaseLiveProjection264.project [owner] [output] after = target ∧
      target ≠ GeneralRebaseLiveProjection264.project [owner] [output] initial :=
  GeneralRebaseRawObserver297.strict_exact reachable metadata safe_exact program_covers observed [owner] [output] target

end Yulang.GeneralRebaseRawDepthReplay297
