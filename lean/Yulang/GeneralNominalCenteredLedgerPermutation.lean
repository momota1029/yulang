import Yulang.GeneralNominalSharedLedgerPermutation
import Yulang.GeneralNominalJournalK2Permutation

/-! The centered ledger uses the same packet pairing as legacy readbacks.
Input centers stay literal; plan equations and tests are transported separately. -/
namespace Yulang.GeneralNominalCenteredLedgerPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalLedgerPermutation (All₂ PacketObservation Coherent)
open GeneralNominalCommonBridge (Assignment)

structure PlanPair (relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop)
    (first last : Plan roles) : Prop where
  packet : relation first.packet last.packet
  input : first.input = last.input
  inputs : ∀ model, GeneralNominalCenteredSupport.Inputs first model ↔ GeneralNominalCenteredSupport.Inputs last model
  outputs : ∀ model, GeneralNominalCenteredSupport.Outputs first model ↔ GeneralNominalCenteredSupport.Outputs last model
  equations : ∀ model, first.Equations model ↔ last.Equations model
  tests : ∀ entry, entry ∈ GeneralNominalCenteredSteps.Plan.tests first ↔ entry ∈ GeneralNominalCenteredSteps.Plan.tests last

namespace PlanPair
variable {roles : Roles.RoleDecls} {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}

theorem left (coherent : Coherent relation) (one : PlanPair relation first middle) (two : PlanPair relation first last) : middle = last := by
  have packets := coherent.left one.packet two.packet
  have inputs := one.input.symm.trans two.input
  cases middle; cases last
  cases packets; cases inputs
  rfl

theorem right (coherent : Coherent relation) (one : PlanPair relation middle last) (two : PlanPair relation first last) : middle = first := by
  have packets := coherent.right one.packet two.packet
  have inputs := one.input.trans two.input.symm
  cases middle; cases first
  cases packets; cases inputs
  rfl
end PlanPair

inductive FactPair (relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop) :
    GeneralNominalCenteredSupport.Fact roles → GeneralNominalCenteredSupport.Fact roles → Prop
  | input : PlanPair relation first last → FactPair relation (.input first) (.input last)
  | output : PlanPair relation first last → FactPair relation (.output first) (.output last)
  | legacy : GeneralNominalLedgerPermutation.FactPair relation first last → FactPair relation (.legacy first) (.legacy last)
  | merge : FactPair relation (.merge first last) (.merge first last)

structure Related (relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop)
    (first last : GeneralNominalCenteredSteps.State roles) : Prop where
  erased : GeneralNominalLedgerPermutation.Related relation first.erased last.erased
  sites : ∀ site, site ∈ first.sites ↔ site ∈ last.sites
  plans : All₂ (PlanPair relation) first.plans last.plans
  roots : first.sourceSites = last.sourceSites

namespace Related
variable {roles : Roles.RoleDecls} {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    {first last : GeneralNominalCenteredSteps.State roles}

theorem models (same : Related relation first last) (model) :
    GeneralNominalCenteredSteps.Models first model ↔ GeneralNominalCenteredSteps.Models last model := by
  have plans : (∀ plan ∈ first.plans, plan.Equations model) ↔ ∀ plan ∈ last.plans, plan.Equations model := by
    constructor
    · intro valid plan member
      obtain ⟨other,found,pair⟩ := GeneralNominalLedgerPermutation.all₂_right same.plans member
      exact (pair.equations model).mp (valid other found)
    · intro valid plan member
      obtain ⟨other,found,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.plans member
      exact (pair.equations model).mpr (valid other found)
  simp only [GeneralNominalCenteredSteps.Models,same.erased.current.models,same.sites,plans]

theorem fact_models (same : Related relation first last) (pair : FactPair relation one two) (model) :
    one.Holds model ↔ two.Holds model := by
  cases pair with
  | input pair => exact pair.inputs model
  | output pair => exact pair.outputs model
  | legacy pair => exact same.erased.coherent.holds pair model
  | merge => exact Iff.rfl

theorem fact_left (same : Related relation first last) (one : FactPair relation a b) (two : FactPair relation a c) : b = c := by
  cases one <;> cases two
  · exact congrArg GeneralNominalCenteredSupport.Fact.input (PlanPair.left same.erased.coherent ‹_› ‹_›)
  · exact congrArg GeneralNominalCenteredSupport.Fact.output (PlanPair.left same.erased.coherent ‹_› ‹_›)
  · exact congrArg GeneralNominalCenteredSupport.Fact.legacy (same.erased.coherent.fact_left ‹_› ‹_›)
  · rfl

theorem fact_right (same : Related relation first last) (one : FactPair relation a c) (two : FactPair relation b c) : a = b := by
  cases one <;> cases two
  · exact congrArg GeneralNominalCenteredSupport.Fact.input (PlanPair.right same.erased.coherent ‹_› ‹_›)
  · exact congrArg GeneralNominalCenteredSupport.Fact.output (PlanPair.right same.erased.coherent ‹_› ‹_›)
  · exact congrArg GeneralNominalCenteredSupport.Fact.legacy (same.erased.coherent.fact_right ‹_› ‹_›)
  · rfl

theorem fact_members (same : Related relation first last) (facts : All₂ (FactPair relation) one two)
    (pair : FactPair relation a b) : a ∈ one ↔ b ∈ two := by
  constructor
  · intro member
    obtain ⟨other,found,actual⟩ := GeneralNominalLedgerPermutation.all₂_left facts member
    exact same.fact_left actual pair ▸ found
  · intro member
    obtain ⟨other,found,actual⟩ := GeneralNominalLedgerPermutation.all₂_right facts member
    exact same.fact_right actual pair ▸ found

theorem facts_models (same : Related relation first last) (facts : All₂ (FactPair relation) one two) (model) :
    GeneralNominalCenteredSupport.Models first.erased first.sourceSites one model ↔
      GeneralNominalCenteredSupport.Models last.erased last.sourceSites two model := by
  have all : (∀ fact ∈ one, fact.Holds model) ↔ ∀ fact ∈ two, fact.Holds model := by
    constructor
    · intro valid fact member
      obtain ⟨other,found,pair⟩ := GeneralNominalLedgerPermutation.all₂_right facts member
      exact (same.fact_models pair model).mp (valid other found)
    · intro valid fact member
      obtain ⟨other,found,pair⟩ := GeneralNominalLedgerPermutation.all₂_left facts member
      exact (same.fact_models pair model).mpr (valid other found)
  simp only [GeneralNominalCenteredSupport.Models,same.erased.source,same.roots,all]

theorem readback (same : Related relation first last) (facts : All₂ (FactPair relation) one two)
    (pair : PlanPair relation plan other) :
    GeneralNominalCenteredSupport.Readback first.erased first.sourceSites one plan ↔
      GeneralNominalCenteredSupport.Readback last.erased last.sourceSites two other := by
  have condition : ∀ state roots facts (plan : Plan roles),
      GeneralNominalCenteredSupport.Readback state roots facts plan ↔
        ∀ observation, GeneralNominalLedgerPermutation.Reads plan.packet observation → ∀ model,
          GeneralNominalCenteredSupport.Models state roots facts model → observation.Holds model := by
    intro state roots facts plan
    exact ⟨fun valid observation ⟨slot,member,test,head⟩ => valid slot member test observation head,
      fun valid slot member test observation head => valid observation ⟨slot,member,test,head⟩⟩
  rw [condition,condition]
  simp only [(same.erased.coherent.sound pair.packet).reads,same.facts_models facts]

theorem trusted {facts : List (GeneralNominalCenteredSupport.Fact roles)} (same : Related relation first last)
    (trusted : GeneralNominalCenteredSupport.Trusted first.erased first.sourceSites first.plans facts) :
    ∃ other, All₂ (FactPair relation) facts other ∧
      GeneralNominalCenteredSupport.Trusted last.erased last.sourceSites last.plans other := by
  induction trusted with
  | source => exact ⟨[],.nil,.source⟩
  | legacy facts readbacks trusted =>
    obtain ⟨other,pairs,trusted⟩ := same.erased.shared_trusted trusted
    refine ⟨other.map .legacy,?_,.legacy other readbacks trusted⟩
    have lift : ∀ {a b}, All₂ (GeneralNominalLedgerPermutation.FactPair relation) a b →
        All₂ (FactPair relation) (a.map .legacy) (b.map .legacy) := by
      intro a b pairs
      induction pairs with
      | nil => exact .nil
      | cons pair pairs ih => exact .cons (.legacy pair) ih
    exact lift pairs
  | input plan support _ member recorded readback ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.plans member
    exact ⟨_,.cons (.input pair) pairs,.input other support trusted present
      ((same.erased.coherent.fact_members same.erased.facts (.inputs pair.packet)).mp recorded)
      ((same.readback pairs pair).mp readback)⟩
  | output plan support _ member recorded included settled ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.plans member
    exact ⟨_,.cons (.output pair) pairs,.output other support trusted present
      ((same.erased.coherent.fact_members same.erased.facts (.outputs pair.packet)).mp recorded)
      ((same.fact_members pairs (.input pair)).mp included) ((same.erased.packet_settled pair.packet).mp settled)⟩
  | merge a b support _ recorded holds inputs ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    have models := funext (fun model => propext (same.facts_models pairs model))
    refine ⟨_,.cons .merge pairs,.merge a b support trusted
      ((same.erased.coherent.fact_members same.erased.facts .merge).mp recorded) ?_ ?_⟩
    · exact fun model valid => holds model ((same.facts_models pairs model).mpr valid)
    · rw [← models]; exact inputs

end Related
end Yulang.GeneralNominalCenteredLedgerPermutation
