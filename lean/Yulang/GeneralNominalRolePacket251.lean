import Yulang.GeneralNominalRoleEmission251
import Yulang.GeneralNominalMixedPacket251
/-! A full finite packet compiler retaining expression roles rather than
collapsing all current reads into one source-name map. -/
namespace Yulang.GeneralNominalRolePacket251
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralNominalRebasePacketView243 (Packet names)
open GeneralNominalRebaseLiveView243 (Argument)
open CommonNominalFullCarrier

def binder (env : Syntax) (name : Nat) : GeneralNominalRebaseLiveView243.Argument :=
 ⟨(env.capture name).lower,(env.capture name).upper,env.binder name⟩

def BinderHolds (values : Values) (name : Nat) : Prop :=
 Subtype (values.lower name) (values.binder name) ∧ Subtype (values.binder name) (values.upper name)

def children (plan : Plan roles) (env : Syntax) : List GeneralNominalRebasePacketView243.Child :=
 plan.packet.declaration.requirements.attach.map fun clause =>
 GeneralNominalRoleChild251.compile plan env clause.val (plan.packet.checked.signature.2.2.2 clause.val clause.property)

def output (plan : Plan roles) (env : Syntax) : GeneralNominalRoleRequests251.Compiled :=
 GeneralNominalRoleRequests251.compile plan.packet.registry.constructors plan.packet.context.interpretation
   plan.packet.declaration.outputNames env (GeneralNominalRoleEmission251.requests plan env)

def Holds (plan : Plan roles) (env : Syntax) (values : Values) (assignment : Assignment) : Prop :=
 GeneralNominalState.Models plan.packet.context.state values.old ∧
 GeneralNominalMixedPacket251.Ordinary plan values.old ∧
 GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) values.old ∧
 plan.input.Holds values.old ∧
 (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name → BinderHolds values name) ∧
 GeneralNominalRoleSchema251.Holds plan.packet.declaration.outputNames plan.headSchema values ∧
 (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
   GeneralNominalRoleChild251.Holds plan env values assignment clause valid) ∧
 ∀ request ∈ GeneralNominalRoleEmission251.requests plan env,
 GeneralNominalRoleRequests251.Holds plan.packet.registry.constructors plan.packet.context.interpretation
   plan.packet.declaration.outputNames values assignment request

def compile (plan : Plan roles) (env : Syntax) : Packet :=
 ⟨GeneralNominalRebaseRawView243.compile plan.packet.context.state env.old,
 (GeneralNominalMixedPacket251.ordinary plan).map (GeneralNominalRebaseRawView243.atom env.old),
 GeneralNominalRebaseProjectionView243.compile plan.packet.context.state env.old (GeneralNominalPacketSupport.report plan.packet),
 GeneralNominalRebaseLiveView243.compile plan.input env.old,(names plan).map (binder env),
 GeneralNominalRoleSchema251.compile plan.packet.declaration.outputNames env plan.headSchema,children plan env,(output plan env).equations⟩

theorem binders_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) :
 (∀ argument ∈ (names plan).map (binder env), argument.Holds assignment) ↔
 ∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name → BinderHolds (read env assignment) name := by
 simp only [List.forall_mem_map,GeneralNominalRebasePacketView243.names_exact]
 rfl

theorem children_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) :
 (∀ child ∈ children plan env, child.Holds assignment) ↔
 ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
 GeneralNominalRoleChild251.Holds plan env (read env assignment) assignment clause valid := by
 simp only [children,List.forall_mem_map,GeneralNominalRoleChild251.compile_exact]
 constructor
 · intro held clause member valid
   exact held ⟨clause,member⟩ (List.mem_attach _ _)
 · intro held clause _
   exact held clause.val clause.property _

theorem compile_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) :
 (compile plan env).Holds assignment ↔ Holds plan env (read env assignment) assignment := by
 unfold compile Packet.Holds Holds output
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseRawView243.all_exact,
   GeneralNominalMixedPacket251.ordinary_exact,GeneralNominalRebaseProjectionView243.compile_exact,
   GeneralNominalRebaseLiveView243.compile_holds,binders_exact,GeneralNominalRoleSchema251.compile_exact,
   children_exact,GeneralNominalRoleRequests251.compile_exact]
 rfl

def Ready (plan : Plan roles) (env : Syntax) : Prop :=
 plan.headSchema.unknown = false ∧
 (∀ request ∈ GeneralNominalRoleEmission251.requests plan env, ∃ expression,
   GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors plan.packet.context.interpretation request.pattern = some expression) ∧
 ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
 ∀ request ∈ GeneralNominalRoleChild251.requests plan env clause valid, ∃ expression,
 GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors plan.packet.context.interpretation request.pattern = some expression

/-- This tests translation readiness only, not eligibility or satisfiability. -/
def ready (plan : Plan roles) (env : Syntax) : Bool :=
 !plan.headSchema.unknown && !(output plan env).unknown &&
 plan.packet.declaration.requirements.attach.all fun clause =>
 !(GeneralNominalRoleRequests251.compile plan.packet.registry.constructors plan.packet.context.interpretation
   plan.packet.declaration.outputNames env (GeneralNominalRoleChild251.requests plan env clause.val
     (plan.packet.checked.signature.2.2.2 clause.val clause.property))).unknown

theorem ready_exact (plan : Plan roles) (env : Syntax) : ready plan env = true ↔ Ready plan env := by
 have not_true (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
 simp only [ready,Bool.and_eq_true,not_true,output,GeneralNominalRoleRequests251.known_iff,List.all_eq_true,Ready]
 constructor
 · rintro ⟨⟨head,outputs⟩,child⟩
   refine ⟨head,outputs,?_⟩
   intro clause member valid
   exact child ⟨clause,member⟩ (List.mem_attach _ _)
 · rintro ⟨head,outputs,child⟩
   exact ⟨⟨head,outputs⟩,fun clause _ => child clause.val clause.property _⟩
end Yulang.GeneralNominalRolePacket251
