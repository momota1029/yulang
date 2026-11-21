import Yulang.GeneralVersionedEqualChildCenters312
import Yulang.GeneralNominalCenteredPointSource

set_option backward.isDefEq.respectTransparency false
/-! Actual current frames are functional for a fixed checked declaration
key and exact occurrence. Numeric identity alone is deliberately insufficient. -/
namespace Yulang.GeneralVersionedCurrentFrame312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedSiteOrigins312 (emitted_origin emitted_above stored_visible)
open GeneralNominalVersionedEvidence231 (Frame)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def ExactRaw (state : State roles) : Prop :=
  ∀ raw ∈ state.core.erased.current.sites, ∃ center ∈ state.core.sites, raw = center.observed

theorem trace_raw
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (path : B4Target.Steps (Step registry root) (initial ctx root) state) :
    ExactRaw state := by
  induction path with
  | refl =>
    intro raw seen
    have same : (rootSite ctx.state.seed root).observed = GeneralNominalDemandMerging.pointSite root :=
      GeneralNominalCenteredPointSource.point_observed _ point (point_center _ _)
    exact ⟨_,List.mem_singleton_self _,(List.mem_singleton.mp seen).trans same.symm⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action =>
      cases action with
      | enqueue _ absent =>
        obtain ⟨x,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial ctx) path).1 generated
        exact False.elim (absent x present same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install e _ _ =>
      intro raw seen
      rcases List.mem_append.mp seen with old|added
      · obtain ⟨center,present,same⟩ := ih raw old
        exact ⟨center,List.mem_append_left _ present,same⟩
      · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
        exact ⟨center,List.mem_append_right _ present,rfl⟩

theorem raw_observed (path : B4TargetV8.Reachable (boundary roles) registry root state) : ExactRaw state := by
  obtain ⟨first,⟨legacy,⟨ctx,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,trace⟩ := path
  subst first
  subst legacy
  exact trace_raw point trace

theorem center_exact
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (same : first.occurrence = last.occurrence) : first = last := by
  obtain ⟨ctx,data⟩ := GeneralVersionedSiteOrigins312.reached path
  have ids := congrArg Occurrence.identity same
  rcases data.origin first one with rfl|⟨a,ha,ea⟩
  · rcases data.origin last two with rfl|⟨b,hb,eb⟩
    · rfl
    · have parent := data.root_le b.input (data.input b hb)
      rw [b.input_exact] at parent
      have above := Nat.lt_of_le_of_lt parent (emitted_above eb)
      exact False.elim (Nat.lt_irrefl _ (ids ▸ above))
  · rcases data.origin last two with rfl|⟨b,hb,eb⟩
    · have parent := data.root_le a.input (data.input a ha)
      rw [a.input_exact] at parent
      have above := Nat.lt_of_le_of_lt parent (emitted_above ea)
      exact False.elim (Nat.lt_irrefl _ (ids ▸ above))
    · obtain ⟨ca,ac,sa,rfl⟩ := emitted_origin ea
      obtain ⟨cb,bc,sb,rfl⟩ := emitted_origin eb
      have seed := (data.configuration a ha).1.trans (data.configuration b hb).1.symm
      exact GeneralVersionedEqualChildCenters312.child_site
        (GeneralNominalCenteredHeadAllocEncoding.registry registry)
        (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
        a b seed (stored_visible path ha) (stored_visible path hb) ca cb ac bc sa sb same

theorem raw_exact
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {first last : GeneralNominalDemandMerging.Site roles}
    (one : first ∈ state.core.erased.current.sites) (two : last ∈ state.core.erased.current.sites)
    (same : first.occurrence = last.occurrence) : first = last := by
  obtain ⟨a,ha,rfl⟩ := raw_observed path first one
  obtain ⟨b,hb,rfl⟩ := raw_observed path last two
  exact congrArg Site.observed (center_exact checked path a b ha hb same)

theorem frame_exact
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    {first last : Plan roles}
    (one : Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry) state.core focus key first)
    (two : Frame (GeneralNominalCenteredHeadAllocEncoding.registry registry) state.core focus key last) :
    first = last := by
  have center := center_exact checked path first.input last.input one.center_recorded two.center_recorded
    ((first.input_exact.trans one.occurrence_eq).trans (last.input_exact.trans two.occurrence_eq).symm)
  have raw := raw_exact checked path one.raw_recorded two.raw_recorded (one.occurrence_eq.trans two.occurrence_eq.symm)
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _
    one.visible two.visible (one.key_eq.trans two.key_eq.symm)
  rcases first with ⟨⟨reg₁,ctx₁,site₁,decl₁,cert₁,bounds₁⟩,input₁,inputEq₁⟩
  rcases last with ⟨⟨reg₂,ctx₂,site₂,decl₂,cert₂,bounds₂⟩,input₂,inputEq₂⟩
  have regEq₁ : reg₁ = GeneralNominalCenteredHeadAllocEncoding.registry registry := one.registry_eq
  have regEq₂ : reg₂ = GeneralNominalCenteredHeadAllocEncoding.registry registry := two.registry_eq
  have ctxEq₁ : ctx₁ = state.core.erased.current.context := one.context_eq
  have ctxEq₂ : ctx₂ = state.core.erased.current.context := two.context_eq
  have declEq : decl₁ = decl₂ := declaration
  have siteEq : site₁ = site₂ := raw
  have centerEq : input₁ = input₂ := center
  subst reg₁; subst reg₂; subst ctx₁; subst ctx₂
  subst decl₂; subst site₂; subst input₂
  have boundsEq : bounds₁ = bounds₂ := Option.some.inj (one.located.symm.trans two.located)
  subst bounds₂
  rfl

end Yulang.GeneralVersionedCurrentFrame312
