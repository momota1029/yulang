import Yulang.GeneralNominalInstallableEvidence190

/-! Recursive V6 dictionary soundness from actual operational availability.
The missing hypothesis is explicit: every generated selected head has an actual
Installable certificate in the current state. No general availability theorem
is asserted, and the unchanged boundary is not replaced by a local classifier. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalInstallationSound190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}

/-- Operational residual, not an evidence premise. Frame identifies the source
occurrence, declaration key, current context and actual ordered children. -/
def Available (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus → ∀ key children,
    Local registry state focus (.selected key children) →
    ∃ plan support, Frame registry state.core focus key plan ∧
      plan.packet.children = children ∧ Installable registry state plan support

/-- Stability plus actual availability records child edges, not just their
membership in a separately assumed closure. -/
theorem generated_children (root focus : Occurrence roles)
    (stable : (boundary roles).Stable registry state root)
    (generated : Generated state.core.erased.current root focus)
    (plan : Plan roles) (frame : Frame registry state.core focus key plan)
    (enabled : Installable registry state plan support) :
    ∀ child ∈ plan.packet.children, Generated state.core.erased.current root child := by
  have reached : Generated state.core.erased.current root plan.packet.site.occurrence := by
    rw [frame.occurrence_eq]; exact generated
  have committed := GeneralNominalInstallableEvidence190.generated_committed root stable reached enabled
  intro child member
  exact .child reached (committed.2 child member)

private theorem selected_parts {v : B4Target.Vocabulary} (b : B4TargetV6.SourceBoundary v)
    {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat} {dictionaries : List Dictionary}
    (derived : B4TargetV6.Classify b r s d (.selected (.node key dictionaries))) :
    ∃ children, B4TargetV6.Local b r s d (.selected key children) ∧
      All₂ (fun child dictionary => B4TargetV6.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases derived with
  | selected safe unique clear children => exact ⟨_,.selected safe unique clear,children⟩

mutual
  theorem dictionary_evidence (root : Occurrence roles)
      (stable : (boundary roles).Stable registry state root)
      (available : Available registry state root)
      (model : Assignment) (valid : Models state model)
      (dictionary : Dictionary) (focus : Occurrence roles)
      (generated : Generated state.core.erased.current root focus)
      (derived : B4TargetV6.Classify (boundary roles) registry state focus (.selected dictionary)) :
      (boundary roles).Evidence registry state model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨demands,localRule,children⟩ := selected_parts (boundary roles) derived
      obtain ⟨plan,support,frame,kids,enabled⟩ := available focus generated key demands localRule
      have reached : Generated state.core.erased.current root plan.packet.site.occurrence := by
        rw [frame.occurrence_eq]; exact generated
      have childGenerated := generated_children root focus stable generated plan frame enabled
      have childEvidence := dictionaries_evidence root stable available model valid dictionaries _
        (fun child member => childGenerated child (kids ▸ member)) children
      have result := GeneralNominalInstallableEvidence190.generated_evidence root stable reached enabled model valid
        dictionaries (kids.symm ▸ childEvidence)
      simpa only [frame.occurrence_eq,frame.key_eq] using result
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (root : Occurrence roles)
      (stable : (boundary roles).Stable registry state root)
      (available : Available registry state root)
      (model : Assignment) (valid : Models state model)
      (dictionaries : List Dictionary) (demands : List (Occurrence roles))
      (generated : ∀ child ∈ demands, Generated state.core.erased.current root child)
      (derived : All₂ (fun d dictionary => B4TargetV6.Classify (boundary roles) registry state d (.selected dictionary))
        demands dictionaries) :
      All₂ ((boundary roles).Evidence registry state model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence root stable available model valid _ _ (generated _ (by simp)) first)
        (dictionaries_evidence root stable available model valid _ _
        (fun child member => generated child (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- The conclusion is the real V6 DictionarySound predicate. Availability and
stability at the executor's final state are still unproved general premises. -/
theorem dictionary_sound (executor : B4TargetV3.Executor (GeneralNominalCenteredHeadStepBoundary.vocabulary roles))
    (stable : ∀ registry, (boundary roles).Checked registry → ∀ state root,
      (boundary roles).Initial registry root state → (boundary roles).Stable registry (executor.run registry state root).1 root)
    (available : ∀ registry, (boundary roles).Checked registry → ∀ state root,
      (boundary roles).Initial registry root state → Available registry (executor.run registry state root).1 root) :
    B4TargetV6.DictionarySound (boundary roles) executor := by
  intro registry checked state root dictionary source derived model valid
  exact dictionary_evidence root (stable registry checked state root source)
    (available registry checked state root source) model valid dictionary root .root derived

end Yulang.GeneralNominalInstallationSound190
