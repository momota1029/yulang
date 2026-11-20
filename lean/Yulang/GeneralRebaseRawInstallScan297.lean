import Yulang.GeneralRebaseWitnessContracts297
import Yulang.GeneralNominalCenteredInspection

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRawInstallScan297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable Committed Step)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Honest atFocus observation)
open GeneralRebaseSourceClassification267 (verdict source_valid)
open GeneralRebaseSourceObserver267 (Probes installAt)
open GeneralRebaseNoveltyProbe267 (novel)

abbrev Known (r : Registry) (s : State roles) (f : Occurrence roles) : Prop :=
  B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) (Encoded r) s f

variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles}
  {root f : Occurrence roles} {checked : (Boundary roles).Checked r}
  {probes : Probes roles}

theorem frame_positions {p : Plan roles}
    (safe : Known r s f) (frame : Frame (Encoded r) s.core f k p) :
    GeneralNominalVersionedCycles232.Safe s p := by
  refine ⟨GeneralNominalCenteredInspection.plan_complete p ?_,?_⟩
  · have located := frame.located
    rw [←frame.occurrence_eq,←p.input_exact] at located
    exact located
  · intro entry inPlan cycle
    exact safe.2.2.1 (Or.inr ⟨p,frame.key_eq.symm ▸ frame,entry,inPlan,cycle⟩)

theorem install_from_current {e : Effect roles} (checked : (Boundary roles).Checked r)
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (reg : e.registry = Encoded r) (snap : e.snapshot = s.core)
    (safe : Known r s e.plan.packet.site.occurrence)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current e.plan.packet)
    (common : ∃ m, GeneralNominalVersionedMixedMaterialization237.Residual s e m) :
    Installable (Encoded r) s e := by
  have frame : Frame (Encoded r) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    reg ▸ snap ▸ e.frame
  refine ⟨reg,snap,safe,GeneralNominalVersionedMixedEmbedding234.source_cache reach,
    GeneralNominalVersionedMixedReady235.materialized reach frame,choice,frame_positions safe frame,?_,?_⟩
  · intro alternate _ alternateFrame
    exact frame_positions (e.plan.input_exact.symm ▸ safe) alternateFrame
  · obtain ⟨m,held⟩ := common
    exact ⟨m,(GeneralNominalVersionedMixedMaterialization237.installation_models_iff checked reach reg snap).mpr held⟩

theorem reconstruct
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (generated : Generated s.core.erased.current root f)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (honest : Honest (probes.head f) (atFocus (Encoded r) s root f (declChecked checked)))
    (p : Plan roles) (listed : p ∈ installAt r s root f checked probes) :
    ∃ e : Effect roles, e.registry = Encoded r ∧ e.snapshot = s.core ∧ e.plan = p ∧
      e.plan.packet.site.occurrence = f := by
  obtain ⟨⟨key,kids⟩,chosen,atMember,yes,obs,_,_,_⟩ :=
    (GeneralRebaseInstallCandidates267.scan_exact ..).mp listed
  obtain ⟨ready,focus⟩ := (GeneralRebaseHeadProbe267.atFocus_exact ..).mp atMember
  obtain ⟨shell,_,preflight⟩ := (GeneralRebaseCandidatePrepared267.ready_exact ..).mp ready
  have prepared := (GeneralRebaseCandidatePrepared267.prepared_iff _ _ _ _ shell).mpr
    ⟨metadata,preflight,honest.positive p atMember yes⟩
  have frame := GeneralRebaseEnumeratePlans267.frame_of_member (Encoded r) s root (declChecked checked)
     p ((GeneralRebaseEnumeratePlans267.plans_exact ..).mpr shell) prepared
  have uniqueFound := source_valid r s root f checked reach generated metadata (probes.head f) honest
  rw [chosen] at uniqueFound
  change Unique (Encoded r) s.core.erased.current.context f key kids at uniqueFound
  obtain ⟨keyEq,childrenEq⟩ := Prod.mk.inj obs
  have exactUnique : Unique (Encoded r) s.core.erased.current.context p.packet.site.occurrence
      p.packet.declaration.id (GeneralNominalVersionedFrame231.children p.packet) := by
    rwa [focus,keyEq,childrenEq]
  let e := GeneralRebaseSourceSelect267.effectFromPlan (Encoded r) s p frame exactUnique
    (GeneralNominalVersionedMixedReady235.ready checked reach frame)
  exact ⟨e,rfl,rfl,rfl,focus⟩

theorem selected_raw
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (generated : Generated s.core.erased.current root f)
    (metadata : Metadata (Encoded r) s.core.erased.current.context) (safe : Known r s f)
    (honest : Honest (probes.head f) (atFocus (Encoded r) s root f (declChecked checked)))
    (contracts : GeneralRebaseInstallCandidates267.Probes (Encoded r) s
      (probes.novelty f) (probes.joint f) (atFocus (Encoded r) s root f (declChecked checked)))
    (p : Plan roles) (listed : p ∈ installAt r s root f checked probes) :
    ∃ e : Effect roles, e.plan = p ∧ e.plan.packet.site.occurrence = f ∧
      Installable (Encoded r) s e ∧ ¬ Committed s e.plan := by
  obtain ⟨e,reg,snap,planEq,atFocusHere⟩ := reconstruct reach generated metadata honest p listed
  obtain ⟨_,_,atSource,_,_,choice,novelty,joint⟩ :=
    (GeneralRebaseInstallCandidates267.scan_exact ..).mp listed
  exact ⟨e,planEq,atFocusHere,install_from_current (checked := checked) reach reg snap (atFocusHere.symm ▸ safe)
      (planEq.symm ▸ (GeneralRebaseInstallChecks267.choice_exact ..).mp choice)
      (contracts.jointSound p atSource joint e reg snap planEq),
    planEq.symm ▸ GeneralRebaseNoveltyProbe267.sound s _ p (contracts.novelSound p atSource) novelty⟩

end Yulang.GeneralRebaseRawInstallScan297
