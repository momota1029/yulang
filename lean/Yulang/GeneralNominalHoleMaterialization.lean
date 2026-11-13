import Yulang.GeneralNominalHoleFacets

/-! Mode-sensitive endpoint readback through the actual schema consumer.
Lower/upper uses read lattice facets; actual uses retain shared observations. -/
namespace Yulang.GeneralNominalHoleMaterialization
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalHoleFacets
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable {model : Assignment}

def At (models : Assignment → Prop) (basis : List Nat) (origin : Origin) (term : Facet Nat) : Prop :=
  (∀ model, models model → (∃ value, Observes model origin value) ∧
    ∀ value, Observes model origin value → Equivalent value (term.eval (fun name => (model name).1))) ∧
      ∀ name ∈ term.leaves, name ∈ basis

def endpoint (capture : GeneralDeclarationDemands.Capture) (name : Nat) : Mode → Option Nat
  | .lower => some (capture.inputs name).1
  | .upper => some (capture.inputs name).2
  | .actual => none

theorem endpoint_use (valid : GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (input : entry.name ∉ declaration.outputNames)
    (selected : endpoint capture entry.name entry.mode = some identity) :
    (∃ value, Observes model entry.origin value) ∧
      ∀ value, Observes model entry.origin value → Equivalent value (model identity).1 := by
  have use := valid.2.1 entry member
  refine ⟨use.1,?_⟩
  intro value observed
  have equation := use.2 value observed
  cases mode : entry.mode <;> simp only [mode,endpoint,Option.some.injEq,reduceCtorEq] at selected
  · subst identity
    simpa only [VariableHolds,input,ite_false,mode] using equation
  · subst identity
    simpa only [VariableHolds,input,ite_false,mode] using equation

theorem materialized_endpoint
    (valid : ∀ model, models model → GeneralNominalMaterialization.Models state declaration capture report body model)
    (member : entry ∈ body.variables) (input : entry.name ∉ declaration.outputNames)
    (selected : endpoint capture entry.name entry.mode = some identity)
    (readback : Over models basis identity term) : At models basis entry.origin term := by
  refine ⟨?_,readback.2⟩
  intro model holds
  have use := endpoint_use (valid model holds) member input selected
  refine ⟨use.1,?_⟩
  intro value observed
  have one := use.2 value observed
  have two := readback.1 model holds
  exact ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

theorem source_exact : At models basis (.source identity) term ↔ Over models basis identity term := by
  constructor
  · intro readback
    exact ⟨fun model valid => (readback.1 model valid).2 _ (.source identity),readback.2⟩
  · intro readback
    refine ⟨fun model valid => ⟨⟨_,.source identity⟩,?_⟩,readback.2⟩
    intro value seen
    cases seen
    exact readback.1 model valid

theorem compose (readback : At models middle origin term) (substitution : Nat → Facet Nat)
    (represented : ∀ name ∈ middle, Over models basis name (substitution name)) :
    At models basis origin (term.bind substitution) := by
  refine ⟨?_,?_⟩
  · intro model valid
    have old := readback.1 model valid
    have replaced := eval_bind term substitution (fun name => (model name).1) (fun name => (model name).1)
      (fun name member => (represented name (readback.2 name member)).1 model valid)
    refine ⟨old.1,?_⟩
    intro value seen
    have same := old.2 value seen
    exact ⟨subtype_trans same.1 replaced.1,subtype_trans replaced.2 same.2⟩
  · intro name member
    obtain ⟨prior,present,member⟩ := (GeneralNominalHoleFacets.leaves_bind term substitution name).mp member
    exact (represented prior (readback.2 prior present)).2 name member

theorem packet_lower (packet : GeneralNominalSaturationState.Packet roles)
    (entry : Use) (member : entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables)
    (mode : entry.mode = .lower) (input : entry.name ∉ packet.declaration.outputNames)
    (declared : entry.name ∈ packet.declaration.inputNames) :
    At (GeneralNominalPacketSupport.Inputs packet)
      ((GeneralNominalAllocation.occurrences packet.bindings entry.name).map Prod.fst)
      entry.origin (lowerFacet (GeneralNominalAllocation.occurrences packet.bindings entry.name)) := by
  apply materialized_endpoint (fun _ valid => valid.2.2) member input
    (by simp only [mode,endpoint]) (packet_endpoints packet entry.name declared).1

theorem packet_upper (packet : GeneralNominalSaturationState.Packet roles)
    (entry : Use) (member : entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables)
    (mode : entry.mode = .upper) (input : entry.name ∉ packet.declaration.outputNames)
    (declared : entry.name ∈ packet.declaration.inputNames) :
    At (GeneralNominalPacketSupport.Inputs packet)
      ((GeneralNominalAllocation.occurrences packet.bindings entry.name).map Prod.snd)
      entry.origin (upperFacet (GeneralNominalAllocation.occurrences packet.bindings entry.name)) := by
  apply materialized_endpoint (fun _ valid => valid.2.2) member input
    (by simp only [mode,endpoint]) (packet_endpoints packet entry.name declared).2

end Yulang.GeneralNominalHoleMaterialization
