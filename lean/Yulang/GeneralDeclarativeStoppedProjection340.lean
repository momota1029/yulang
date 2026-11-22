import Yulang.GeneralDeclarativeStoppedIntervals340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedProjection340
open GeneralNominalState (State)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralDeclarativeStoppedLower339 (headAt)
open GeneralDeclarativeStoppedStructural339 (encode meaning)
open GeneralStoppedLower335 (collect collect_exact normal record record_exact holds)
open GeneralNominalRebaseRawView243 (all_exact)
open GeneralDeclarativeStoppedIntervals340 (Row table table_exact)
open Core.PresenceGeneration (CompTerm)
open CommonNominalFullCarrier (Equivalent)

structure View where
  ordinary : GeneralDeclarativeHead320.State
  intervals : List Row

def Models (v : View) (m : Assignment) : Prop :=
  GeneralDeclarativeHead320.Models v.ordinary m ∧
    ∀ row ∈ v.intervals, GeneralDeclarativeStoppedIntervals340.Holds m row

def project (raw : State) : Option View :=
  (collect (headAt raw) (List.ofFn (fun k : Fin raw.base.slots => k))).map
    (fun es => ⟨⟨normal raw,es⟩,table raw⟩)

theorem head_exact (raw : State) (k : Fin raw.base.slots) (m : Assignment)
    (computed : headAt raw k = some es) :
    holds m es ↔ ∀ t, (raw.base.heads k).equation = some t →
      Equivalent (m (raw.base.source k)).1
        (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m)) :=
  record_exact (recorded := (raw.base.heads k).equation)
    (check := fun t => Equivalent (m (raw.base.source k)).1
      (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m)))
    (m := m) (fun t expr e => by rw [meaning raw.base m t e]) computed

/-- Same, arbitrary assignment on both sides; interval-side data is not
simulated by equations choosing points for invariant parameters. -/
theorem exact_models (raw : State) (m : Assignment) (computed : project raw = some v) :
    Models v m ↔ GeneralNominalState.Models raw m := by
  unfold project at computed
  obtain ⟨es,found,rfl⟩ := Option.map_eq_some_iff.mp computed
  have head := collect_exact (f := headAt raw) (m := m) _
    (fun k _ saved => head_exact raw k m saved) found
  unfold Models GeneralDeclarativeHead320.Models GeneralDeclarativeWhere319.Models
    GeneralNominalState.Models GeneralNominalCommonBridge.Models
  change (((PresenceNormalForm.All _ m ((raw.base.ordinary.map _) ++ raw.ordinary) ∧ _) ∧ holds m es) ∧ _) ↔ _
  rw [PresenceNormalForm.all_append,all_exact,head,table_exact]
  constructor
  · rintro ⟨⟨⟨⟨ordinary,extra⟩,bounds⟩,shapes⟩,nominal⟩
    refine ⟨⟨ordinary,fun k => shapes k (List.mem_ofFn.mpr ⟨k,rfl⟩),?_⟩,nominal,extra⟩
    intro pair member
    exact bounds (raw.base.source pair.1,raw.base.source pair.2) (List.mem_map_of_mem member)
  · rintro ⟨⟨ordinary,heads,bounds⟩,nominal,extra⟩
    refine ⟨⟨⟨⟨ordinary,extra⟩,?_⟩,fun k _ => heads k⟩,nominal⟩
    intro pair member
    obtain ⟨ab,there,rfl⟩ := List.mem_map.mp member
    exact bounds ab there

def append (v : View) (new : List Equation) : View :=
  { v with ordinary := GeneralDeclarativeEntailment320.appendFacts v.ordinary new }

theorem append_exact (v : View) (new : List Equation) (m : Assignment) :
    Models (append v new) m ↔
      Models v m ∧ ∀ e ∈ new, GeneralDeclarativeEntailment320.Holds m e := by
  unfold Models append
  rw [GeneralDeclarativeEntailment320.model_append m]
  exact ⟨fun ⟨⟨old,added⟩,nominal⟩ => ⟨⟨old,nominal⟩,added⟩,
    fun ⟨⟨old,nominal⟩,added⟩ => ⟨⟨old,added⟩,nominal⟩⟩

end Yulang.GeneralDeclarativeStoppedProjection340
