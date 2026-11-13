import Yulang.GeneralNominalPacketSupport

/-! The semantic report uses persistent source IDs, not transient Fin slots.
Capture multiplicity and order are retained exactly. -/
namespace Yulang.GeneralNominalReportErasure
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

structure CaptureData where
  name : Nat
  bounds : GeneralSourceState.Interval
  origin : Option Origin

structure Data where
  captures : List CaptureData := []
  checked : List GeneralSourceState.Interval := []
  anchors : List (Origin × GeneralSourceState.Interval) := []
  tests : List (Origin × Test) := []

def interval (state : GeneralNominalState.State) (bounds : GeneralNominalInspection.Bounds state) :
    GeneralSourceState.Interval := (state.base.source bounds.1,state.base.source bounds.2)

def erase (state : GeneralNominalState.State) (report : Report state) : Data :=
  ⟨report.captures.map (fun entry => ⟨entry.name,interval state entry.bounds,entry.origin⟩),
    report.checked.map (interval state),
    report.anchors.map (fun entry => (entry.1,interval state entry.2)),report.tests⟩

def Data.append (first last : Data) : Data :=
  ⟨first.captures ++ last.captures,first.checked ++ last.checked,
    first.anchors ++ last.anchors,first.tests ++ last.tests⟩

def Data.visit (bounds : GeneralSourceState.Interval) (origin : Option Origin) (test : Test) (data : Data) : Data :=
  {data with
    checked := bounds :: data.checked,
    anchors := origin.toList.map (fun ref => (ref,bounds)) ++ data.anchors,
    tests := origin.toList.map (fun ref => (ref,test)) ++ data.tests}

def Data.bindings (data : Data) : GeneralNominalAllocation.Bindings :=
  data.captures.map fun entry => (entry.name,entry.bounds)

def Data.selfChecks (data : Data) : List (PresenceNormalForm.Atom Nat) :=
  data.checked.map fun bounds => .tyLe (.var bounds.1) (.var bounds.2)

def Data.Projections (data : Data) (model : Assignment) : Prop :=
  (∀ anchor ∈ data.anchors, (∃ actual, Observes model anchor.1 actual) ∧
    ∀ actual, Observes model anchor.1 actual → GeneralNominalCaptureMerges.Fits model anchor.2 actual) ∧
  (∀ test ∈ data.tests, ∀ actual, Observes model test.1 actual → test.2.Holds actual) ∧
  (∀ first ∈ data.captures, ∀ last ∈ data.captures, first.name = last.name →
    ∀ ref, first.origin = some ref → ∀ actual, Observes model ref actual →
      GeneralNominalCaptureMerges.Fits model last.bounds actual) ∧
  (∀ first ∈ data.captures, ∀ last ∈ data.captures, first.name = last.name →
    ∀ a b, first.origin = some a → last.origin = some b →
    ∀ x y, Observes model a x → Observes model b y → Equivalent x y)

def Data.Materialized (data : Data) (declaration : GeneralDeclarations.Declaration)
    (capture : GeneralDeclarationDemands.Capture) (body : Schema) (model : Assignment) : Prop :=
  (∀ test ∈ body.tests, (∃ actual, Observes model test.1 actual) ∧
    ∀ actual, Observes model test.1 actual → test.2.Holds actual) ∧
  (∀ entry ∈ body.variables, (∃ actual, Observes model entry.origin actual) ∧
    ∀ actual, Observes model entry.origin actual → VariableHolds declaration capture model entry.name entry.mode actual) ∧
  (∀ first ∈ body.variables, ∀ last ∈ body.variables, first.name = last.name → first.mode = .actual → last.mode = .actual →
    ∀ a b, Observes model first.origin a → Observes model last.origin b → Equivalent a b) ∧
  (∀ entry ∈ body.variables, ∀ captured ∈ data.captures, entry.name = captured.name → entry.mode = .actual →
    ∀ origin, captured.origin = some origin → ∀ a b,
      Observes model entry.origin a → Observes model origin b → Equivalent a b)

theorem erase_empty (state : GeneralNominalState.State) : erase state {} = {} := rfl
theorem erase_append (state : GeneralNominalState.State) (first last : Report state) :
    erase state (first.append last) = (erase state first).append (erase state last) := by
  simp [erase,Report.append,Data.append,List.map_append]
theorem erase_visit (state : GeneralNominalState.State) (bounds) (origin) (test) (report : Report state) :
    erase state (Report.visit bounds origin test report) = Data.visit (interval state bounds) origin test (erase state report) := by
  simp [erase,Report.visit,Data.visit,List.map_append,List.map_map,Function.comp_def]
theorem bindings_exact (state : GeneralNominalState.State) (report : Report state) :
    (erase state report).bindings = bindings state report := by
  simp [erase,Data.bindings,bindings,List.map_map,interval]
theorem checks_exact (state : GeneralNominalState.State) (report : Report state) :
    (erase state report).selfChecks = selfChecks state report := by
  simp [erase,Data.selfChecks,selfChecks,List.map_map,interval]

theorem projections_exact (state : GeneralNominalState.State) (report : Report state) (model : Assignment) :
    (erase state report).Projections model ↔ ProjectionModels state report model := by
  constructor
  · rintro ⟨anchors,tests,cross,coherent⟩
    refine ⟨?_,tests,?_,?_⟩
    · intro anchor member
      exact anchors _ (List.mem_map.mpr ⟨anchor,member,rfl⟩)
    · intro first one last two same ref recorded actual seen
      exact cross _ (List.mem_map.mpr ⟨first,one,rfl⟩) _
        (List.mem_map.mpr ⟨last,two,rfl⟩) same ref recorded actual seen
    · intro first one last two same a b left right x y seen observed
      exact coherent _ (List.mem_map.mpr ⟨first,one,rfl⟩) _
        (List.mem_map.mpr ⟨last,two,rfl⟩) same a b left right x y seen observed
  · rintro ⟨anchors,tests,cross,coherent⟩
    refine ⟨?_,tests,?_,?_⟩
    · intro anchor member
      obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
      exact anchors old present
    · intro first one last two same ref recorded actual seen
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp one
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp two
      exact cross a ha b hb same ref recorded actual seen
    · intro first one last two same a b left right x y seen observed
      obtain ⟨prior,hp,rfl⟩ := List.mem_map.mp one
      obtain ⟨later,hl,rfl⟩ := List.mem_map.mp two
      exact coherent prior hp later hl same a b left right x y seen observed

theorem materialized_exact (state : GeneralNominalState.State) (report : Report state)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (body : Schema) (model : Assignment) :
    (erase state report).Materialized declaration capture body model ↔
      GeneralNominalMaterialization.Models state declaration capture report body model := by
  simp [Data.Materialized,erase,GeneralNominalMaterialization.Models]

theorem actual_capture_retained (state : GeneralNominalState.State) (report : Report state)
    (entry : Capture state) (member : entry ∈ report.captures) :
    (⟨entry.name,interval state entry.bounds,entry.origin⟩ : CaptureData) ∈ (erase state report).captures :=
  List.mem_map.mpr ⟨entry,member,rfl⟩

theorem packet_delta_exact (packet : GeneralNominalSaturationState.Packet roles) (model : Assignment) :
    (GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model) ↔
      GeneralNominalPacketSupport.Ordinary packet model ∧
      (erase packet.context.state (GeneralNominalPacketSupport.report packet)).Projections model ∧
      (erase packet.context.state (GeneralNominalPacketSupport.report packet)).Materialized packet.declaration
        (GeneralNominalPacketSupport.capture packet) (GeneralNominalPacketSupport.namedSchema packet) model := by
  rw [projections_exact,materialized_exact]
  constructor
  · exact fun valid => ⟨valid.1.1,valid.1.2.1,valid.2⟩
  · exact fun valid => ⟨⟨valid.1,valid.2.1,GeneralNominalPacketSupport.outputs_inputs packet model valid.2.2⟩,valid.2.2⟩

end Yulang.GeneralNominalReportErasure
