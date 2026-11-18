import Yulang.GeneralNominalProjectionSchemaSubst249
import Yulang.GeneralNominalRebaseClassView243
import Yulang.GeneralNominalRebaseObservedSite243
import Yulang.GeneralNominalRebasePacketView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalPacketSubst249
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebasePacketView243

def equation (mapping : Nat → CompTerm Nat) (e : GeneralNominalRebaseEffectView243.Equation) :
 GeneralNominalRebaseEffectView243.Equation :=
 ⟨e.target.subst mapping,GeneralNominalRebaseEffectView243.subst mapping e.expression⟩
def child (mapping : Nat → CompTerm Nat) (c : Child) : Child :=
 ⟨c.site.subst mapping,c.equations.map (equation mapping)⟩
def packet (mapping : Nat → CompTerm Nat) (p : Packet) : Packet :=
 ⟨GeneralNominalRebaseViewSubst243.subst p.raw mapping,
 p.ordinary.map (GeneralNominalRebaseRawView243.atom mapping),
 GeneralNominalProjectionSchemaSubst249.report mapping p.projection,
 p.input.subst mapping,p.binders.map (fun a => a.subst mapping),
 GeneralNominalProjectionSchemaSubst249.schema mapping p.head,
 p.children.map (child mapping),p.outputs.map (equation mapping)⟩

theorem equation_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (e : GeneralNominalRebaseEffectView243.Equation) :
 (equation mapping e).Holds assignment ↔ e.Holds (read mapping assignment) := by
 simp only [equation,GeneralNominalRebaseEffectView243.Equation.Holds,TyTerm.eval_subst,
   GeneralNominalRebaseEffectView243.subst_exact]
 rfl

theorem equations_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (es : List GeneralNominalRebaseEffectView243.Equation) :
 AllEquations (es.map (equation mapping)) assignment ↔ AllEquations es (read mapping assignment) := by
 simp only [AllEquations,List.forall_mem_map,equation_exact]

theorem child_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (c : Child) :
 (child mapping c).Holds assignment ↔ c.Holds (read mapping assignment) :=
 and_congr (GeneralNominalRebaseLiveView243.site_subst c.site mapping assignment) (equations_exact mapping assignment c.equations)

theorem packet_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (p : Packet) :
 (packet mapping p).Holds assignment ↔ p.Holds (read mapping assignment) := by
 simp only [packet,Packet.Holds,GeneralNominalRebaseViewSubst243.exact,
   GeneralNominalRebaseRawView243.all_exact,GeneralNominalProjectionSchemaSubst249.report_exact,
   GeneralNominalRebaseLiveView243.site_subst,List.forall_mem_map,
   GeneralNominalRebaseLiveView243.argument_subst,GeneralNominalProjectionSchemaSubst249.schema_exact,
   child_exact,equations_exact]
 rfl

def classView (mapping : Nat → CompTerm Nat) (v : GeneralNominalRebaseClassView243.View) :
 GeneralNominalRebaseClassView243.View :=
 ⟨v.equations.map (equation mapping),v.equalities.map (GeneralNominalRebaseRawView243.atom mapping)⟩

theorem class_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment) (v : GeneralNominalRebaseClassView243.View) :
 (classView mapping v).Holds assignment ↔ v.Holds (read mapping assignment) := by
 simp only [classView,GeneralNominalRebaseClassView243.View.Holds,List.forall_mem_map,
   equation_exact,GeneralNominalRebaseRawView243.all_exact]
 rfl

def observedArgument (mapping : Nat → CompTerm Nat) (a : GeneralNominalRebaseObservedSite243.Argument) :
 GeneralNominalRebaseObservedSite243.Argument :=
 ⟨GeneralNominalProjectionSchemaSubst249.bounds mapping a.bounds,
 a.origin.map (GeneralNominalRebaseOriginView243.subst mapping)⟩

theorem observed_argument_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment)
 (a : GeneralNominalRebaseObservedSite243.Argument) :
 (observedArgument mapping a).Holds assignment ↔ a.Holds (read mapping assignment) := by
 unfold observedArgument GeneralNominalRebaseObservedSite243.Argument.Holds
 rw [GeneralNominalProjectionSchemaSubst249.option_forall]
 simp only [GeneralNominalRebaseOriginView243.subst_exact,GeneralNominalProjectionSchemaSubst249.bounds_exact]

theorem observed_exact (mapping : Nat → CompTerm Nat) (assignment : Assignment)
 (arguments : List GeneralNominalRebaseObservedSite243.Argument) :
 GeneralNominalRebaseObservedSite243.Holds (arguments.map (observedArgument mapping)) assignment ↔
 GeneralNominalRebaseObservedSite243.Holds arguments (read mapping assignment) := by
 simp only [GeneralNominalRebaseObservedSite243.Holds,List.forall_mem_map,observed_argument_exact]
end Yulang.GeneralNominalPacketSubst249
