import Yulang.GeneralRebasePlanTransport262
namespace Yulang.GeneralRebaseBinderShape262
open GeneralNominalCenters

/-- Either the actual captured point name remains the same, or both captures
remain nonpoint. Their lower/upper endpoints can otherwise change. A transition
from nonpoint to point is deliberately not asserted to preserve the binder. -/
def Compatible (first last : Plan roles) : Prop :=
 ∀ name, name ∉ first.packet.declaration.outputNames →
 (∃ point, (GeneralNominalPacketSupport.capture first.packet).inputs name = (point,point) ∧
   (GeneralNominalPacketSupport.capture last.packet).inputs name = (point,point)) ∨
 (((GeneralNominalPacketSupport.capture first.packet).inputs name).1 ≠
   ((GeneralNominalPacketSupport.capture first.packet).inputs name).2 ∧
  ((GeneralNominalPacketSupport.capture last.packet).inputs name).1 ≠
   ((GeneralNominalPacketSupport.capture last.packet).inputs name).2)

theorem outputs (first last : Plan roles)
 (declaration : first.packet.declaration = last.packet.declaration)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity) (name : Nat) :
 (GeneralNominalPacketSupport.capture first.packet).outputs name =
 (GeneralNominalPacketSupport.capture last.packet).outputs name := by
 unfold GeneralNominalPacketSupport.capture GeneralNominalAllocation.capture GeneralNominalAllocation.source
 simp only [seed,identity,declaration]

theorem binders (first last : Plan roles)
 (declaration : first.packet.declaration = last.packet.declaration)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (compatible : Compatible first last) (name : Nat) : first.binder name = last.binder name := by
 by_cases output : name ∈ first.packet.declaration.outputNames
 · have lastOutput : name ∈ last.packet.declaration.outputNames := declaration ▸ output
   simp only [Plan.binder,output,lastOutput,ite_true]
   exact outputs first last declaration seed identity name
 · have lastInput : name ∉ last.packet.declaration.outputNames := declaration ▸ output
   simp only [Plan.binder,output,lastInput,ite_false]
   rcases compatible name output with ⟨point,one,two⟩ | ⟨one,two⟩
   · simp only [one,two,ite_true]
   · simp only [one,two,ite_false,seed,identity,declaration]

/-- Structural capture classification discharges the actual-binder field of
Plan transport. This is not a proof that every source transition is compatible. -/
theorem transport (first last : Plan roles)
 (declaration : first.packet.declaration = last.packet.declaration)
 (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
 (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
 (seed : first.packet.context.state.seed = last.packet.context.state.seed)
 (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
 (centers : List.ofFn first.input.center = List.ofFn last.input.center)
 (compatible : Compatible first last) : GeneralRebasePlanTransport262.Same first last :=
 ⟨declaration,constructors,interpretation,binders first last declaration seed identity compatible,centers⟩
end Yulang.GeneralRebaseBinderShape262
