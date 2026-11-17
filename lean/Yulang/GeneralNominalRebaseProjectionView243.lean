import Yulang.GeneralNominalRebaseOriginView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseProjectionView243
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralNominalRecursiveInspection (Test)
open CommonNominalFullCarrier

structure Bounds where
 lower : TyTerm Nat
 upper : TyTerm Nat

def Bounds.Fits (bounds : Bounds) (model : Assignment) (actual : Ty) : Prop :=
 Subtype (bounds.lower.eval CommonNominalFullCarrier.model model) actual ∧
 Subtype actual (bounds.upper.eval CommonNominalFullCarrier.model model)

structure Capture where
 name : Nat
 bounds : Bounds
 origin : Option Origin

structure Report where
 anchors : List (Origin × Bounds)
 tests : List (Origin × Test)
 captures : List Capture

def Report.Models (report : Report) (model : Assignment) : Prop :=
 (∀ anchor ∈ report.anchors, (∃ actual, Observes model anchor.1 actual) ∧
   ∀ actual, Observes model anchor.1 actual → anchor.2.Fits model actual) ∧
 (∀ test ∈ report.tests, ∀ actual, Observes model test.1 actual → test.2.Holds actual) ∧
 (∀ first ∈ report.captures, ∀ last ∈ report.captures, first.name = last.name →
   ∀ ref, first.origin = some ref → ∀ actual, Observes model ref actual → last.bounds.Fits model actual) ∧
 (∀ first ∈ report.captures, ∀ last ∈ report.captures, first.name = last.name →
   ∀ a b, first.origin = some a → last.origin = some b →
   ∀ x y, Observes model a x → Observes model b y → Equivalent x y)

def bounds (state : GeneralNominalState.State) (mapping : Nat → CompTerm Nat)
 (pair : GeneralNominalInspection.Bounds state) : Bounds :=
 ⟨(mapping (state.base.source pair.1)).1,(mapping (state.base.source pair.2)).1⟩

def capture (state : GeneralNominalState.State) (mapping : Nat → CompTerm Nat)
 (entry : GeneralNominalRecursiveInspection.Capture state) : Capture :=
 ⟨entry.name,bounds state mapping entry.bounds,entry.origin.map (GeneralNominalRebaseOriginView243.compile mapping)⟩

def compile (state : GeneralNominalState.State) (mapping : Nat → CompTerm Nat)
 (report : GeneralNominalRecursiveInspection.Report state) : Report :=
 ⟨report.anchors.map (fun anchor => (GeneralNominalRebaseOriginView243.compile mapping anchor.1,bounds state mapping anchor.2)),
   GeneralNominalRebaseOriginView243.compileTests mapping report.tests,report.captures.map (capture state mapping)⟩

theorem bounds_exact (state : GeneralNominalState.State) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (pair : GeneralNominalInspection.Bounds state) (actual : Ty) :
 (bounds state mapping pair).Fits model actual ↔ GeneralNominalRecursiveInspection.Fits state (read mapping model) pair actual := Iff.rfl

theorem origin_forall (mapping : Nat → CompTerm Nat) (origin : Option GeneralNominalRecursiveInspection.Origin)
 (property : Origin → Prop) :
 (∀ ref, origin.map (GeneralNominalRebaseOriginView243.compile mapping) = some ref → property ref) ↔
 ∀ ref, origin = some ref → property (GeneralNominalRebaseOriginView243.compile mapping ref) := by
 cases origin with
 | none => simp
 | some value => simp

theorem compile_exact (state : GeneralNominalState.State) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (report : GeneralNominalRecursiveInspection.Report state) :
 (compile state mapping report).Models model ↔ GeneralNominalRecursiveInspection.ProjectionModels state report (read mapping model) := by
 unfold Report.Models compile GeneralNominalRecursiveInspection.ProjectionModels
 simp only [List.forall_mem_map,GeneralNominalRebaseOriginView243.compileTests,
   GeneralNominalRebaseOriginView243.compile_exact,bounds_exact,capture]
 apply and_congr Iff.rfl
 apply and_congr Iff.rfl
 apply and_congr
 · apply forall_congr'; intro first
   apply forall_congr'; intro one
   apply forall_congr'; intro last
   apply forall_congr'; intro two
   apply forall_congr'; intro same
   rw [origin_forall]
   simp only [GeneralNominalRebaseOriginView243.compile_exact]
 · apply forall_congr'; intro first
   apply forall_congr'; intro one
   apply forall_congr'; intro last
   apply forall_congr'; intro two
   apply forall_congr'; intro same
   cases first.origin <;> cases last.origin <;>
     simp [GeneralNominalRebaseOriginView243.compile_exact]
end Yulang.GeneralNominalRebaseProjectionView243
