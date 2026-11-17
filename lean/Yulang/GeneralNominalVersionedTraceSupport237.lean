import Yulang.GeneralNominalVersionedResidualSupportSteps237
import Yulang.GeneralNominalVersionedMixedProgressSplit236
set_option backward.isDefEq.respectTransparency false
/-! Every actual source trace admits a finite support derivation that ignores
semantically redundant refresh/reobserve/equate atom growth. -/
namespace Yulang.GeneralNominalVersionedTraceSupport237
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedModelSupport237 (Support Observation)
open GeneralNominalVersionedModelSupportSteps237 (mergeSources)
open GeneralNominalVersionedResidualSupportSteps237 (installSources)
open GeneralNominalVersionedMixedKernel234
variable {roles : Roles.RoleDecls}

inductive Derivation : State roles → List Nat → State roles → List Nat → Prop
 | refl (state) (names) : Derivation state names state names
 | observation {start before after : State roles} {names current : List Nat} : Derivation start names before current → Observation before after →
     Derivation start names after current
 | merge {start before : State roles} {names current : List Nat} (one two : GeneralNominalCenters.Site roles) : Derivation start names before current →
     Derivation start names (GeneralNominalVersionedAdministrative232.merge before one two)
       (current ++ mergeSources before one two)
 | install {start before : State roles} {names current : List Nat} (effect : Effect roles) : Derivation start names before current → effect.snapshot = before.core →
     Derivation start names (GeneralNominalVersionedInstall232.install before effect)
       (current ++ installSources before effect)

variable {before after : State roles}

theorem supported (trace : Derivation before names after finalNames) (initial : Support before names) :
 Support after finalNames := by
 induction trace with
 | refl => exact initial
 | observation _ action ih =>
     exact GeneralNominalVersionedModelSupport237.transport
       (GeneralNominalVersionedModelSupport237.observation_models action) (ih initial)
 | merge one two _ ih => exact GeneralNominalVersionedModelSupportSteps237.merge _ one two (ih initial)
 | install effect _ snapshot ih => exact GeneralNominalVersionedResidualSupportSteps237.install snapshot (ih initial)

theorem grows (trace : Derivation before names after finalNames) : names ⊆ finalNames := by
 induction trace with
 | refl => exact fun _ h => h
 | observation _ _ ih => exact ih
 | merge _ _ _ ih => exact fun _ h => List.mem_append_left _ (ih h)
 | install _ _ _ ih => exact fun _ h => List.mem_append_left _ (ih h)

abbrev Reachable (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (state : State roles) := B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state

theorem step (path : Reachable registry root before)
 (action : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root before after)
 (prior : Derivation start names before current) : ∃ finalNames, Derivation start names after finalNames := by
 rcases GeneralNominalVersionedMixedProgressSplit236.split path action with update | ⟨effect,enabled,_,rfl⟩
 · cases update with
   | refresh context certificate source member unknown known =>
       exact ⟨current,.observation prior (.refresh _ context certificate)⟩
   | reobserve revision certificate improved =>
       exact ⟨current,.observation prior (.reobserve _ revision certificate)⟩
   | equate first last one two equal novel =>
       exact ⟨current,.observation prior (.equate _ first last equal)⟩
   | merge first last one two same novel => exact ⟨_,.merge first last prior⟩
 · exact ⟨_,.install effect prior enabled.snapshot_eq⟩

theorem append_steps {relation : α → α → Prop} {a b c : α}
 (first : B4Target.Steps relation a b) (last : B4Target.Steps relation b c) :
 B4Target.Steps relation a c := by
 induction last with
 | refl => exact first
 | tail _ action ih => exact .tail ih action

theorem steps (reachable : Reachable registry root before)
 (path : B4Target.Steps (Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root) before after) :
 ∃ finalNames, Derivation before names after finalNames := by
 induction path with
 | refl => exact ⟨names,.refl _ _⟩
 | @tail midway final path action ih =>
   obtain ⟨current,prior⟩ := ih
   have reach : Reachable registry root midway := by
     obtain ⟨initial,formed,history⟩ := reachable
     exact ⟨initial,formed,append_steps history path⟩
   exact step reach action prior

theorem source (path : Reachable registry root state) :
 ∃ initial names, (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root initial ∧
   Derivation initial (GeneralNominalVersionedJournalFrame236.sources initial) state names ∧ Support state names := by
 obtain ⟨initial,formed,trace⟩ := path
 obtain ⟨names,derived⟩ := steps (names := GeneralNominalVersionedJournalFrame236.sources initial)
   ⟨initial,formed,.refl⟩ trace
 exact ⟨initial,names,formed,derived,supported derived (GeneralNominalVersionedModelSupport237.current initial)⟩
end Yulang.GeneralNominalVersionedTraceSupport237
