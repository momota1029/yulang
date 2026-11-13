import Yulang.GeneralNominalOriginTerms

/-! Inherited observations survive variable inspection, including strict
intervals. Agreement is required at every repeated head occurrence. -/
namespace Yulang.GeneralNominalSharedCaptures
open GeneralNominalRecursiveInspection GeneralNominalSaturationState
open GeneralNominalMaterialization GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev inheritedReport (packet : Packet roles) : Report packet.context.state :=
  inspectMany packet.context.state
    (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)
    packet.bounds (fun index => (packet.site.inputs[index]?).join) 0

/-- The representative must be recorded, and every repeated capture must have
an agreeing origin. Fits alone cannot establish either condition. -/
def Captured (packet : Packet roles) (models : Assignment → Prop) (name : Nat) (origin : Origin) : Prop :=
  (∃ captured ∈ (inheritedReport packet).captures,
    captured.name = name ∧ captured.origin = some origin) ∧
  ∀ captured ∈ (inheritedReport packet).captures, captured.name = name →
    ∃ other, captured.origin = some other ∧ ∀ model, models model → Same model origin other

def Needed (packet : Packet roles) (name : Nat) : Prop :=
  ∃ clause ∈ packet.declaration.requirements,
    name ∈ GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs clause.arguments)

def InputBound (packet : Packet roles) (name : Nat) (origin : Origin) : Prop :=
  ∀ model, packet.Holds model → (∃ actual, Observes model origin actual) ∧
    ∀ actual, Observes model origin actual → GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture packet).inputs name) actual

def Usable (packet : Packet roles) (name : Nat) (origin : Origin) : Prop :=
  Captured packet packet.Holds name origin ∧ InputBound packet name origin

def GenerationGuard (_state : GeneralNominalSupport.Tracked roles) (packet : Packet roles) : Prop :=
  ∀ name, Needed packet name → ∃ origin, Usable packet name origin

/-- Nominal positions of compound inputs use actual-mode materialization.
They must use the inherited substitution before their facts become trusted. -/
def InputCoherence (packet : Packet roles) : Prop :=
  ∀ entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables, entry.mode = .actual →
    ∃ origin, Usable packet entry.name origin ∧
      ∀ model, packet.Holds model → Same model entry.origin origin

theorem empty_input_coherent (empty : (GeneralNominalPacketSupport.inputSchema packet).variables = []) :
    InputCoherence packet := by
  intro entry member
  rw [empty] at member
  cases member

theorem variable_retains (state : GeneralNominalState.State) (names : List Nat)
    (bounds : GeneralNominalInspection.Bounds state) (origin : Option Origin) :
    (inspect state (.variables names) bounds origin).captures =
      names.map (fun name => ⟨name,bounds,origin⟩) := by simp [inspect]

theorem missing_capture_blocks (needed : Needed packet name)
    (missing : ∀ captured ∈ (inheritedReport packet).captures,
      captured.name = name → captured.origin = none) : ¬ GenerationGuard state packet := by
  intro guard
  obtain ⟨origin,⟨⟨captured,member,same,recorded⟩,_⟩,_⟩ := guard name needed
  rw [missing captured member same] at recorded
  cases recorded

theorem no_children_guard (empty : packet.declaration.requirements = []) : GenerationGuard state packet := by
  rintro name ⟨clause,member,_⟩
  rw [empty] at member
  cases member

theorem repeated_capture_agrees (known : Captured packet models name origin)
    (first last : Capture packet.context.state)
    (firstMem : first ∈ (inheritedReport packet).captures) (lastMem : last ∈ (inheritedReport packet).captures)
    (one : first.name = name) (two : last.name = name) (model : Assignment) (valid : models model) :
    ∃ a b, first.origin = some a ∧ last.origin = some b ∧ Same model a b := by
  obtain ⟨a,firstOrigin,left⟩ := known.2 first firstMem one
  obtain ⟨b,lastOrigin,right⟩ := known.2 last lastMem two
  exact ⟨a,b,firstOrigin,lastOrigin,same_trans (same_symm (left model valid)) (right model valid)⟩

/-- A forwarded variable carries the origin itself, not its interval endpoints.
This frame is also usable for a nonpoint inherited input. -/
def forward (substitution : Nat → Option Origin) (pattern : GeneralDeclarationPatterns.Pattern) : Option Origin :=
  match GeneralDeclarationPatterns.normalize pattern with
  | .var name => substitution name
  | _ => none

theorem forward_variable (substitution : Nat → Option Origin) (name : Nat) :
    forward substitution (.var name) = substitution name := rfl

variable {model : Assignment}

theorem point_use (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (actual : entry.mode = .actual)
    (input : entry.name ∉ declaration.outputNames) (point : capture.inputs entry.name = (identity,identity)) :
    Same model entry.origin (.source identity) := by
  have use := valid.2.1 entry member
  refine ⟨use.1,⟨_,.source identity⟩,?_⟩
  intro a b seen other
  cases other
  have fitted := use.2 a seen
  have fitted : Subtype (model identity).1 a ∧ Subtype a (model identity).1 := by
    simpa [VariableHolds,input,actual,point,GeneralNominalCaptureMerges.Fits] using fitted
  exact ⟨fitted.2,fitted.1⟩

theorem retained_use (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (actual : entry.mode = .actual)
    (captured : Capture state) (capturedMem : captured ∈ report.captures) (same : entry.name = captured.name)
    (recorded : captured.origin = some origin) (existsValue : ∃ value, Observes model origin value) :
    Same model entry.origin origin :=
  ⟨(valid.2.1 entry member).1,existsValue,
    fun a b one two => valid.2.2.2 entry member captured capturedMem same actual origin recorded a b one two⟩

theorem output_binder_use (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (output : entry.name ∈ declaration.outputNames) :
    Same model entry.origin (.source (capture.outputs entry.name)) := by
  have use := valid.2.1 entry member
  refine ⟨use.1,⟨_,.source _⟩,?_⟩
  intro a b one two
  cases two
  simpa [VariableHolds,output] using use.2 a one

/-- Coherence is obtained from local variable certificates and the unchanged
schema tests. Whole-output readback is the conclusion of recipe_readback. -/
theorem coherent_of_uses (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (uses : ∀ entry ∈ body.variables, entry.mode = .actual → Holds model (substitution entry.name) entry.origin) :
    Coherent model body substitution := ⟨valid.1,uses⟩

end Yulang.GeneralNominalSharedCaptures
