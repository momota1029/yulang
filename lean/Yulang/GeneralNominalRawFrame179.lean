import Yulang.GeneralNominalCenteredEmptyFrame179

/-! Finite syntactic support for raw reports and generated constraints. -/
namespace Yulang.GeneralNominalRawFrame179
open GeneralDeclarations GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
variable {first last : Assignment}

 def reportSources (state : GeneralNominalState.State) (report : Report state) : List Nat :=
  GeneralNominalState.sources state ++ report.anchors.map (fun a => originSource a.1) ++
    report.tests.map (fun t => originSource t.1) ++
    report.captures.flatMap (fun c => c.origin.toList.map originSource)

 theorem report_slot (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) (slot : Fin state.base.slots) :
    first (state.base.source slot) = last (state.base.source slot) := by
  have member : state.base.source slot ∈ GeneralNominalState.sources state :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
  exact same _ (by simp [reportSources,member])

 theorem report_capture (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last)
    (capture : GeneralNominalRecursiveInspection.Capture state) (member : capture ∈ report.captures)
    (origin : Origin) (recorded : capture.origin = some origin) :
    first (originSource origin) = last (originSource origin) := by
  have item : originSource origin ∈ report.captures.flatMap (fun c => c.origin.toList.map originSource) :=
    List.mem_flatMap.mpr ⟨capture,member,by simp [recorded]⟩
  exact same _ (by simp [reportSources,item])

 theorem projection_iff (state : GeneralNominalState.State) (report : Report state)
    (same : Agree (reportSources state report) first last) :
    ProjectionModels state report first ↔ ProjectionModels state report last := by
  have slots := report_slot state report same
  unfold ProjectionModels
  apply and_congr
  · apply forall_congr'; intro anchor
    apply forall_congr'; intro member
    have item : originSource anchor.1 ∈ report.anchors.map (fun a => originSource a.1) :=
      List.mem_map.mpr ⟨anchor,member,rfl⟩
    have root := same _ (by simp [reportSources,item] : originSource anchor.1 ∈ reportSources state report)
    simp only [observes_iff anchor.1 root,Fits,GeneralNominalCaptureMerges.Fits,slots]
  apply and_congr
  · apply forall_congr'; intro test
    apply forall_congr'; intro member
    have item : originSource test.1 ∈ report.tests.map (fun t => originSource t.1) :=
      List.mem_map.mpr ⟨test,member,rfl⟩
    have root := same _ (by simp [reportSources,item] : originSource test.1 ∈ reportSources state report)
    simp only [observes_iff test.1 root]
  apply and_congr
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro _bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro origin
    apply forall_congr'; intro recorded
    have root := report_capture state report same a am origin recorded
    simp only [observes_iff origin root,Fits,GeneralNominalCaptureMerges.Fits,slots]
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro bm
    apply forall_congr'; intro _names
    apply forall_congr'; intro x
    apply forall_congr'; intro y
    apply forall_congr'; intro ax
    apply forall_congr'; intro byy
    simp only [observes_iff x (report_capture state report same a am x ax),
      observes_iff y (report_capture state report same b bm y byy)]

 def useSources (capture : GeneralDeclarationDemands.Capture) (entry : Use) : List Nat :=
  [originSource entry.origin,capture.outputs entry.name,(capture.inputs entry.name).1,(capture.inputs entry.name).2]

 def generatedSources (capture : GeneralDeclarationDemands.Capture) (schema : Schema) : List Nat :=
  schema.tests.map (fun test => originSource test.1) ++ schema.variables.flatMap (useSources capture)

 theorem use_root (capture : GeneralDeclarationDemands.Capture) (schema : Schema)
    (same : Agree (generatedSources capture schema) first last) (entry : Use) (member : entry ∈ schema.variables) :
    first (originSource entry.origin) = last (originSource entry.origin) :=
  same _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,member,by simp [useSources]⟩))

 theorem variable_iff (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture) (entry : Use)
    (same : Agree (useSources capture entry) first last) (actual : CommonNominalFullCarrier.Ty) :
    VariableHolds declaration capture first entry.name entry.mode actual ↔
      VariableHolds declaration capture last entry.name entry.mode actual := by
  have output := same (capture.outputs entry.name) (by simp [useSources])
  have lower := same (capture.inputs entry.name).1 (by simp [useSources])
  have upper := same (capture.inputs entry.name).2 (by simp [useSources])
  simp only [VariableHolds,GeneralNominalCaptureMerges.Fits,output,lower,upper]

 theorem materialization_iff (state : GeneralNominalState.State) (declaration : Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : Report state) (schema : Schema)
    (rsame : Agree (reportSources state report) first last)
    (same : Agree (generatedSources capture schema) first last) :
    GeneralNominalMaterialization.Models state declaration capture report schema first ↔
      GeneralNominalMaterialization.Models state declaration capture report schema last := by
  unfold GeneralNominalMaterialization.Models
  apply and_congr
  · apply forall_congr'; intro test
    apply forall_congr'; intro member
    exact head_iff _ _ (same _ (List.mem_append_left _ (List.mem_map.mpr ⟨test,member,rfl⟩)))
  apply and_congr
  · apply forall_congr'; intro entry
    apply forall_congr'; intro member
    have root := use_root capture schema same entry member
    have values : Agree (useSources capture entry) first last :=
      fun name present => same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,member,present⟩))
    simp only [observes_iff entry.origin root,variable_iff declaration capture entry values]
  apply and_congr
  · apply forall_congr'; intro a
    apply forall_congr'; intro am
    apply forall_congr'; intro b
    apply forall_congr'; intro bm
    simp only [observes_iff a.origin (use_root capture schema same a am),
      observes_iff b.origin (use_root capture schema same b bm)]
  · apply forall_congr'; intro entry
    apply forall_congr'; intro member
    apply forall_congr'; intro captured
    apply forall_congr'; intro present
    apply forall_congr'; intro _name
    apply forall_congr'; intro _mode
    apply forall_congr'; intro origin
    apply forall_congr'; intro recorded
    simp only [observes_iff entry.origin (use_root capture schema same entry member),
      observes_iff origin (report_capture state report rsame captured present origin recorded)]

open GeneralNominalRecursiveCandidates GeneralNominalSaturationState

 def packetSources (packet : Packet roles) : List Nat :=
  GeneralNominalState.sources packet.privateContext.state ++
    reportSources packet.context.state (report packet.context packet.declaration packet.bounds) ++
    generatedSources (GeneralNominalPacketSupport.capture packet)
      (generated packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds)

 theorem packet_iff (packet : Packet roles) (same : Agree (packetSources packet) first last) :
    packet.Holds first ↔ packet.Holds last := by
  have sourceSame : Agree (GeneralNominalState.sources packet.privateContext.state) first last :=
    fun name member => same name (by simp [packetSources,member])
  have sourceIff : GeneralNominalState.Models packet.privateContext.state first ↔
      GeneralNominalState.Models packet.privateContext.state last :=
    ⟨source_models_same _ sourceSame,source_models_same _ (fun name member => (sourceSame name member).symm)⟩
  have rsame : Agree (reportSources packet.context.state (report packet.context packet.declaration packet.bounds)) first last :=
    fun name member => same name (by simp [packetSources,member])
  have gsame : Agree (generatedSources (GeneralNominalPacketSupport.capture packet)
      (generated packet.registry packet.context packet.site.occurrence packet.declaration packet.checked packet.bounds)) first last :=
    fun name member => same name (by simp [packetSources,member])
  exact and_congr sourceIff (and_congr (projection_iff _ _ rsame)
    (materialization_iff _ _ _ _ _ rsame gsame))

 def rawSources (state : GeneralNominalSaturationState.State roles) : List Nat :=
  GeneralNominalState.sources state.context.state ++ state.packets.flatMap packetSources ++
    state.sites.flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources

 theorem raw_models_frame (state : GeneralNominalSaturationState.State roles)
    (same : Agree (rawSources state) first last) (valid : GeneralNominalSaturationState.Models state first) :
    GeneralNominalSaturationState.Models state last := by
  refine ⟨source_models_same state.context.state
    (fun name member => same name (by simp [rawSources,member])) valid.1,?_,?_⟩
  · intro packet member
    apply (packet_iff packet ?_).mp (valid.2.1 packet member)
    intro name present
    have item : name ∈ state.packets.flatMap packetSources := List.mem_flatMap.mpr ⟨packet,member,present⟩
    exact same name (by simp [rawSources,item])
  · intro site member
    apply (GeneralNominalCenteredEmptyFrame179.raw_site_iff site ?_).mp (valid.2.2 site member)
    intro name present
    have item : name ∈ state.sites.flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources :=
      List.mem_flatMap.mpr ⟨site,member,present⟩
    exact same name (by simp [rawSources,item])

 def fullSources (state : GeneralNominalCenteredSteps.State roles) : List Nat :=
  rawSources state.erased.current ++ ledgerSources state

 theorem centered_models_frame (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (fullSources state) first last)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state last :=
  ledger_frame state (fun name member => same name (List.mem_append_right _ member)) valid
    (raw_models_frame state.erased.current (fun name member => same name (List.mem_append_left _ member)) valid.1)

 theorem centered_models_iff (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (fullSources state) first last) :
    GeneralNominalCenteredSteps.Models state first ↔ GeneralNominalCenteredSteps.Models state last :=
  ⟨centered_models_frame state same,
    centered_models_frame state (fun name member => (same name member).symm)⟩

 theorem centered_assign (state : GeneralNominalCenteredSteps.State roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ fullSources state)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state (assign first names values) :=
  centered_models_frame state (assign_agree names values _ outside) valid

/-- Reused source/binder names are permitted if their old values are retained.
Only names inside the finite old footprint need this condition. -/
 theorem centered_assign_kept (state : GeneralNominalCenteredSteps.State roles)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (kept : ∀ index, names index ∈ fullSources state → values index = (first (names index)).1)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state (assign first names values) := by
  apply centered_models_frame state ?_ valid
  intro name member
  apply Eq.symm
  apply assign_preserves
  intro index equal
  simpa only [equal] using kept index (equal.symm ▸ member)

end Yulang.GeneralNominalRawFrame179
