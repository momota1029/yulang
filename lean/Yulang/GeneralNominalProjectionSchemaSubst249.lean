import Yulang.GeneralNominalRebaseSchemaView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalProjectionSchemaSubst249
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseProjectionView243
open GeneralNominalRebaseSchemaView243
open GeneralNominalRebaseOriginView243 (Origin Observes)

def bounds (mapping : Nat → CompTerm Nat) (b : Bounds) : Bounds :=
 ⟨b.lower.subst mapping,b.upper.subst mapping⟩
def capture (mapping : Nat → CompTerm Nat) (c : Capture) : Capture :=
 ⟨c.name,bounds mapping c.bounds,c.origin.map (GeneralNominalRebaseOriginView243.subst mapping)⟩
def report (mapping : Nat → CompTerm Nat) (r : Report) : Report :=
 ⟨r.anchors.map (fun a => (GeneralNominalRebaseOriginView243.subst mapping a.1,bounds mapping a.2)),
 r.tests.map (fun t => (GeneralNominalRebaseOriginView243.subst mapping t.1,t.2)),r.captures.map (capture mapping)⟩

theorem bounds_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (b : Bounds) (actual) :
 (bounds mapping b).Fits assignment actual ↔ b.Fits (read mapping assignment) actual := by
 simp only [bounds,Bounds.Fits,TyTerm.eval_subst]
 rfl

theorem option_forall (mapping : Nat → CompTerm Nat) (origin : Option Origin) (property : Origin → Prop) :
 (∀ ref, origin.map (GeneralNominalRebaseOriginView243.subst mapping) = some ref → property ref) ↔
 ∀ ref, origin = some ref → property (GeneralNominalRebaseOriginView243.subst mapping ref) := by
 cases origin <;> simp

theorem report_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (r : Report) :
 (report mapping r).Models assignment ↔ r.Models (read mapping assignment) := by
 unfold Report.Models report
 simp only [List.forall_mem_map,GeneralNominalRebaseOriginView243.subst_exact,bounds_exact,capture]
 apply and_congr Iff.rfl
 apply and_congr Iff.rfl
 apply and_congr
 · apply forall_congr'; intro first
   apply forall_congr'; intro one
   apply forall_congr'; intro last
   apply forall_congr'; intro two
   apply forall_congr'; intro same
   rw [option_forall]
   simp only [GeneralNominalRebaseOriginView243.subst_exact]
 · apply forall_congr'; intro first
   apply forall_congr'; intro one
   apply forall_congr'; intro last
   apply forall_congr'; intro two
   apply forall_congr'; intro same
   cases first.origin <;> cases last.origin <;> simp [GeneralNominalRebaseOriginView243.subst_exact]

def requirement (mapping : Nat → CompTerm Nat) : Requirement → Requirement
 | .equal term => .equal (term.subst mapping)
 | .interval lo hi => .interval (lo.subst mapping) (hi.subst mapping)
def use (mapping : Nat → CompTerm Nat) : Use → Use
 | .same a b => .same (GeneralNominalRebaseOriginView243.subst mapping a) (GeneralNominalRebaseOriginView243.subst mapping b)
 | .observed origin req => .observed (GeneralNominalRebaseOriginView243.subst mapping origin) (requirement mapping req)
def schema (mapping : Nat → CompTerm Nat) (s : Schema) : Schema :=
 ⟨s.tests.map (fun t => (GeneralNominalRebaseOriginView243.subst mapping t.1,t.2)),s.uses.map (use mapping),s.unknown⟩

theorem requirement_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (r : Requirement) (actual) :
 (requirement mapping r).Holds assignment actual ↔ r.Holds (read mapping assignment) actual := by
 cases r <;> simp only [requirement,Requirement.Holds,TyTerm.eval_subst] <;> rfl

theorem use_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (u : Use) :
 (use mapping u).Holds assignment ↔ u.Holds (read mapping assignment) := by
 cases u with
 | same a b => exact GeneralNominalRebaseOriginView243.same_subst mapping assignment a b
 | observed origin req => simp only [use,Use.Holds,GeneralNominalRebaseOriginView243.subst_exact,requirement_exact]

theorem schema_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (s : Schema) :
 (schema mapping s).Holds assignment ↔ s.Holds (read mapping assignment) := by
 simp only [schema,Schema.Holds,List.forall_mem_map,GeneralNominalRebaseOriginView243.head_subst,use_exact]
end Yulang.GeneralNominalProjectionSchemaSubst249
