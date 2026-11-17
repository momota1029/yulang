import Yulang.GeneralNominalRebaseProjectionView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseProjectionSubst244
open GeneralNominalRebaseProjectionView243
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralNominalRebaseRawView243 (read)
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
def bounds (mapping : Nat → CompTerm Nat) (source : Bounds) : Bounds :=
 ⟨source.lower.subst mapping,source.upper.subst mapping⟩
def capture (mapping : Nat → CompTerm Nat) (source : Capture) : Capture :=
 ⟨source.name,bounds mapping source.bounds,source.origin.map (GeneralNominalRebaseOriginView243.subst mapping)⟩
def subst (source : Report) (mapping : Nat → CompTerm Nat) : Report :=
 ⟨source.anchors.map (fun pair => (GeneralNominalRebaseOriginView243.subst mapping pair.1,bounds mapping pair.2)),
 source.tests.map (fun pair => (GeneralNominalRebaseOriginView243.subst mapping pair.1,pair.2)),
 source.captures.map (capture mapping)⟩
theorem bounds_exact (mapping : Nat → CompTerm Nat) (source : Bounds) (model : Assignment) (actual) :
 (bounds mapping source).Fits model actual ↔ source.Fits (read mapping model) actual := by
 simp only [bounds,Bounds.Fits,Core.PresenceGeneration.TyTerm.eval_subst]
 rfl
theorem option_forall (mapping : Nat → CompTerm Nat) (origin : Option Origin) (property : Origin → Prop) :
 (∀ ref, origin.map (GeneralNominalRebaseOriginView243.subst mapping) = some ref → property ref) ↔
 (∀ ref, origin = some ref → property (GeneralNominalRebaseOriginView243.subst mapping ref)) := by
 cases origin <;> simp
theorem exact (source : Report) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (subst source mapping).Models model ↔ source.Models (read mapping model) := by
 unfold subst Report.Models
 simp only [List.forall_mem_map,capture]
 simp only [option_forall,GeneralNominalRebaseOriginView243.subst_exact,bounds_exact]
 apply and_congr Iff.rfl
 apply and_congr Iff.rfl
 apply and_congr Iff.rfl
 apply forall_congr'; intro first
 apply forall_congr'; intro _
 apply forall_congr'; intro last
 apply forall_congr'; intro _
 apply forall_congr'; intro _
 cases first.origin <;> cases last.origin <;> simp [GeneralNominalRebaseOriginView243.subst_exact]
end Yulang.GeneralNominalRebaseProjectionSubst244
