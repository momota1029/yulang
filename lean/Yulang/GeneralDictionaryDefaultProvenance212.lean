import Yulang.GeneralDictionaryDefaultSelectedGeneration211
import Yulang.GeneralDictionaryDefaultConfiguration209
import Yulang.GeneralNominalIdentityJournal

set_option backward.isDefEq.respectTransparency false

/-! Inverse registration provenance for every actual corrected trace.
No selection, shape, point-interval or model premise is required. -/
namespace Yulang.GeneralDictionaryDefaultProvenance212
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
variable {roles : Roles.RoleDecls} {state : State roles}

 theorem raw_origin
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites,
      site.occurrence = root ∨ ∃ plan ∈ state.core.plans, site.occurrence ∈ plan.packet.children := by
  induction path with
  | refl =>
      intro site member
      cases List.mem_singleton.mp member
      exact Or.inl rfl
  | @tail before after path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,present,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                (GeneralDictionaryDefaultTrace208.registered_trace path) generated
              exact False.elim (absent site present same)
          | refresh | equate | reobserve => exact ih
      | refresh | merge => exact ih
      | install effect enabled novel =>
          intro site member
          change site ∈ before.core.erased.current.sites ++ effect.plan.emitted.map Site.observed at member
          rcases List.mem_append.mp member with old | added
          · rcases ih site old with root | ⟨plan,present,child⟩
            · exact Or.inl root
            · exact Or.inr ⟨plan,List.mem_cons_of_mem _ present,child⟩
          · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
            obtain ⟨clause,_,rfl⟩ := List.mem_map.mp present
            exact Or.inr ⟨effect.plan,List.mem_cons_self ..,
              GeneralNominalCenteredTrace.clauseChild_mem effect.plan.packet clause.val clause.property
                (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property)⟩

 theorem root_le_registered
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites, root.identity ≤ site.occurrence.identity := by
  induction path with
  | refl =>
      intro site member
      cases List.mem_singleton.mp member
      exact Nat.le_refl _
  | @tail before after path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,present,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                (GeneralDictionaryDefaultTrace208.registered_trace path) generated
              exact False.elim (absent site present same)
          | refresh | equate | reobserve => exact ih
      | refresh | merge => exact ih
      | install effect enabled novel =>
          intro site member
          change site ∈ before.core.erased.current.sites ++ effect.plan.emitted.map Site.observed at member
          rcases List.mem_append.mp member with old | added
          · exact ih site old
          · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
            obtain ⟨clause,_,rfl⟩ := List.mem_map.mp present
            have frame := enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame
            exact Nat.le_trans (ih effect.plan.packet.site frame.raw_recorded)
              (Nat.le_of_lt (GeneralNominalIdentityJournal.child_parent effect.plan.packet clause.val
                (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property)))

end Yulang.GeneralDictionaryDefaultProvenance212

namespace Yulang.GeneralDictionaryDefaultProvenance212
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- One evidenced child forces an installed parent with this invocation and
implementation identity. Parent endpoint equality is deliberately not claimed. -/
 theorem child_registered_parent
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : child ∈ current.packet.children)
    (registered : ∃ site ∈ state.core.erased.current.sites, site.occurrence = child) :
    ∃ historical ∈ state.core.plans,
      historical.packet.site.occurrence.identity = focus.identity ∧
      historical.packet.declaration = current.packet.declaration := by
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  obtain ⟨clause,present,signature,childEq⟩ :=
    GeneralNominalPatersonLineage.emitted_clause current.packet child member
  have above := Nat.lt_of_le_of_lt (root_le_registered path current.packet.site frame.raw_recorded)
    (GeneralNominalIdentityJournal.child_parent current.packet clause signature)
  obtain ⟨site,recorded,same⟩ := registered
  rcases raw_origin path site recorded with isRoot | ⟨historical,stored,oldChild⟩
  · have equal : child = root := same.symm.trans isRoot
    rw [← childEq,equal] at above
    exact False.elim (Nat.lt_irrefl _ above)
  · rw [same] at oldChild
    obtain ⟨oldClause,oldPresent,oldSignature,oldEq⟩ :=
      GeneralNominalPatersonLineage.emitted_clause historical.packet child oldChild
    have oldData := GeneralDictionaryDefaultConfiguration209.stored built stored
    have record := GeneralDictionaryDefaultRecorded208.recorded
      (show B4TargetV7.Reachable (boundary roles) value root state from
        ⟨_,initial,path⟩)
    obtain ⟨effect,effectMem,effectPlan⟩ := record.2 historical stored
    have visible : historical.packet.declaration ∈ (registry value).declarations := by
      rw [← effectPlan]
      have reg := effect.frame.registry_eq.symm.trans (effectPlan ▸ oldData.1)
      exact reg ▸ effect.frame.visible
    have seed : current.packet.context.state.seed = historical.packet.context.state.seed :=
      ((congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
        (GeneralDictionaryDefaultConfiguration209.seed built)).trans oldData.2.1.symm
    have collision := GeneralNominalIdentityJournal.child_collision
      (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 current.packet historical.packet
      frame.visible visible seed clause oldClause signature oldSignature
      (congrArg Occurrence.identity (childEq.symm.trans oldEq))
    exact ⟨historical,stored,collision.1.symm.trans (congrArg Occurrence.identity frame.occurrence_eq),collision.2.symm⟩

end Yulang.GeneralDictionaryDefaultProvenance212
