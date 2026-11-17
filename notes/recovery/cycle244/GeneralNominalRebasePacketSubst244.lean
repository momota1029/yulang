import Yulang.GeneralNominalRebaseProjectionSubst244
import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalRebaseViewSubst243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebasePacketSubst244
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseSchemaView243 (Requirement Use Schema)
open GeneralNominalRebaseEffectView243 (Equation)
open GeneralNominalRebasePacketView243 (Packet Child AllEquations)
def requirement (mapping : Nat → CompTerm Nat) : Requirement → Requirement
 | .equal term => .equal (term.subst mapping)
 | .interval lo hi => .interval (lo.subst mapping) (hi.subst mapping)
def use (mapping : Nat → CompTerm Nat) : Use → Use
 | .same a b => .same (GeneralNominalRebaseOriginView243.subst mapping a) (GeneralNominalRebaseOriginView243.subst mapping b)
 | .observed origin req => .observed (GeneralNominalRebaseOriginView243.subst mapping origin) (requirement mapping req)
def schema (mapping : Nat → CompTerm Nat) (source : Schema) : Schema :=
 ⟨source.tests.map (fun pair => (GeneralNominalRebaseOriginView243.subst mapping pair.1,pair.2)),
 source.uses.map (use mapping),source.unknown⟩
theorem requirement_exact (mapping : Nat → CompTerm Nat) (source : Requirement) (model : Assignment) (actual) :
 (requirement mapping source).Holds model actual ↔ source.Holds (read mapping model) actual := by
 cases source <;> simp only [requirement,Requirement.Holds,Core.PresenceGeneration.TyTerm.eval_subst] <;> rfl
theorem use_exact (mapping : Nat → CompTerm Nat) (source : Use) (model : Assignment) :
 (use mapping source).Holds model ↔ source.Holds (read mapping model) := by
 cases source <;> simp only [use,Use.Holds,GeneralNominalRebaseOriginView243.same_subst,
   GeneralNominalRebaseOriginView243.subst_exact,requirement_exact]
theorem schema_exact (mapping : Nat → CompTerm Nat) (source : Schema) (model : Assignment) :
 (schema mapping source).Holds model ↔ source.Holds (read mapping model) := by
 simp only [schema,Schema.Holds,List.forall_mem_map,GeneralNominalRebaseOriginView243.head_subst,use_exact]
theorem unknown_kept (mapping : Nat → CompTerm Nat) (source : Schema) :
 (schema mapping source).unknown = source.unknown := rfl
def equation (mapping : Nat → CompTerm Nat) (source : Equation) : Equation :=
 ⟨source.target.subst mapping,GeneralNominalRebaseEffectView243.subst mapping source.expression⟩
theorem equation_exact (mapping : Nat → CompTerm Nat) (source : Equation) (model : Assignment) :
 (equation mapping source).Holds model ↔ source.Holds (read mapping model) := by
 unfold equation Equation.Holds
 rw [Core.PresenceGeneration.TyTerm.eval_subst,GeneralNominalRebaseEffectView243.subst_exact]
 rfl
theorem equations_exact (mapping : Nat → CompTerm Nat) (sources : List Equation) (model : Assignment) :
 AllEquations (sources.map (equation mapping)) model ↔ AllEquations sources (read mapping model) := by
 simp only [AllEquations,List.forall_mem_map,equation_exact]
def child (mapping : Nat → CompTerm Nat) (source : Child) : Child :=
 ⟨source.site.subst mapping,source.equations.map (equation mapping)⟩
theorem child_exact (mapping : Nat → CompTerm Nat) (source : Child) (model : Assignment) :
 (child mapping source).Holds model ↔ source.Holds (read mapping model) := by
 exact and_congr (GeneralNominalRebaseLiveView243.site_subst source.site mapping model) (equations_exact mapping source.equations model)
def subst (source : Packet) (mapping : Nat → CompTerm Nat) : Packet :=
 ⟨GeneralNominalRebaseViewSubst243.subst source.raw mapping,
 source.ordinary.map (GeneralNominalRebaseRawView243.atom mapping),
 GeneralNominalRebaseProjectionSubst244.subst source.projection mapping,
 source.input.subst mapping,source.binders.map (fun argument => argument.subst mapping),
 schema mapping source.head,source.children.map (child mapping),source.outputs.map (equation mapping)⟩
theorem exact (source : Packet) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (subst source mapping).Holds model ↔ source.Holds (read mapping model) := by
 simp only [subst,Packet.Holds,GeneralNominalRebaseViewSubst243.exact,GeneralNominalRebaseRawView243.all_exact,
 GeneralNominalRebaseProjectionSubst244.exact,GeneralNominalRebaseLiveView243.site_subst,List.forall_mem_map,
 GeneralNominalRebaseLiveView243.argument_subst,schema_exact,child_exact,equations_exact]
 rfl
end Yulang.GeneralNominalRebasePacketSubst244
