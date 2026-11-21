import Yulang.GeneralVersionedHistoricalJoint312

set_option backward.isDefEq.respectTransparency false
/-! A current head binder is either a directly read point or a private
purpose-8 name. The former needs no external write, and distinct new binders
cannot collide. Only a protected private binder needs a reuse justification. -/
namespace Yulang.GeneralVersionedBinderTargets312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAllocation (occurrences)
open CommonNominalFullCarrier
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalOriginTerms (same_trans same_symm)
open GeneralVersionedAliasHeadWrites312 (rows pool)
open GeneralFiniteTypedWrites312 (Coherent Protected transitive symmetric reflexive)
variable {roles : Roles.RoleDecls}

abbrev actualName (p : Plan roles) (name : Nat) := fresh p.packet.context.state.seed
  p.packet.site.occurrence.identity p.packet.declaration.id 8 name 0

theorem cases_binder (p : Plan roles) (name : Nat) (input : name ∈ p.packet.declaration.inputNames) :
    (∃ point, occurrences p.packet.bindings name = [(point,point)] ∧ binder p name = point) ∨
      binder p name = actualName p name := by
  have noOutput := GeneralNominalHeadSchemaNames186.input_not_output p name input
  unfold binder
  simp only [noOutput,ite_false]
  unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
  cases found : occurrences p.packet.bindings name with
  | nil =>
    right
    have distinct := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
      p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings (by decide)
    simp only [found,distinct,ite_false]
  | cons head tail =>
    cases tail with
    | nil =>
      rcases head with ⟨a,b⟩
      by_cases equal : a = b
      · subst b
        exact Or.inl ⟨a,rfl,by simp [found]⟩
      · exact Or.inr (by simp [found,equal])
    | cons next tail =>
      right
      have distinct := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
        p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings (by decide)
      simp only [found,distinct,ite_false]

theorem point_binding (p : Plan roles) (name point : Nat)
    (same : occurrences p.packet.bindings name = [(point,point)]) :
    (name,point,point) ∈ p.packet.bindings := by
  have m : (point,point) ∈ occurrences p.packet.bindings name := same ▸ List.mem_singleton_self _
  unfold occurrences at m
  obtain ⟨⟨old,a,b⟩,inside,values⟩ := List.mem_map.mp m
  obtain ⟨bound,named⟩ := List.mem_filter.mp inside
  have h : old = name := beq_iff_eq.mp named
  have e := Prod.mk.inj values
  rcases e with ⟨first,last⟩
  subst a; subst b; subst old
  exact bound

theorem point_in_pool (p : Plan roles) (names : List Nat) (name point : Nat)
    (same : occurrences p.packet.bindings name = [(point,point)]) : point ∈ pool p names := by
  have supported := GeneralNominalReportSupport237.report_endpoints p.packet.context.state
    (GeneralNominalPacketSupport.report p.packet) (name,point,point) (point_binding p name point same)
  have raw : point ∈ GeneralNominalVersionedResidualFrame237.headSources p.packet :=
    List.mem_append_right _ supported.1
  simp [pool,raw]

theorem point_agrees {registry : Registry} {root : Occurrence roles} {s : State roles} {now past : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core focus key now) (stored : past ∈ s.plans)
    (alias : GeneralNominalSaturationState.Alias s.core.erased.current
      now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (sameRule : now.packet.declaration = past.packet.declaration)
    (m : Assignment) (valid : Models s m) (name point : Nat)
    (one : occurrences now.packet.bindings name = [(point,point)]) :
    Equivalent (m point).1 (m (past.binder name)).1 := by
  obtain ⟨tests,actual⟩ := GeneralVersionedAliasReadback312.readback checked path stored
    frame.center_recorded frame.context_eq alias sameRule valid
  have agreement := GeneralDictionaryHeadSharing220.agreement_of_holds now m
    ((GeneralDictionaryHeadSharing220.holds_iff now m).mpr (by
      intro x a y b same
      have v := actual x a
      rw [same] at v
      exact same_trans v (same_symm (actual y b))))
  have locate := frame.occurrence_eq.symm ▸ frame.located
  have projection := (GeneralVersionedAliasReport312.projection_iff now frame.context_eq
    frame.center_recorded locate m valid tests).mpr agreement
  have located := point_binding now name point one
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings now] at located
  obtain ⟨captured,present,cap⟩ := List.mem_map.mp located
  have fields := Prod.mk.inj cap
  have endpoints := Prod.mk.inj fields.2
  obtain ⟨origin,reported,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    now.packet.context.state _ now.packet.bounds _ 0 captured present
  have exact := actual _ used
  rw [fields.1] at exact
  obtain ⟨value,seen⟩ := exact.1
  have bound := (projection.1 _ (GeneralNominalCaptureAnchors.many_anchored now.packet.context.state
    _ now.packet.bounds _ 0 captured present origin reported)).2 value seen
  change Subtype (m _).1 value ∧ Subtype value (m _).1 at bound
  rw [endpoints.1,endpoints.2] at bound
  exact transitive bound (exact.2.2 value _ seen (.source _))

theorem same_fresh_name (p : Plan roles) {a b : Nat} (equal : actualName p a = actualName p b) : a = b :=
  congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.1)
    ((GeneralNominalIdentities.source_identity p.packet.context.state.seed _ _).mp equal)

end Yulang.GeneralVersionedBinderTargets312
