import Yulang.GeneralDictionaryDefaultTerminalOutputs210
import Yulang.GeneralDictionaryActualSchema

/-! Separate report-sensitive head support from persistent actual equations.
Terminal total-packet replay below leaves precisely ordinary constraints,
projections, and interval fits explicit, rather than assuming packet Holds. -/
namespace Yulang.GeneralDictionaryDefaultActualHead210
open GeneralNominalCenters GeneralNominalCenteredHeadMatStepPackets
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem head_schema
    (queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
      first.packet.declaration = GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration)
    (input : first.input = last.input) : first.headSchema = last.headSchema := by
  have centers := congrArg (fun site : Site roles => List.ofFn site.center) input
  simp only [Plan.headSchema,queries,centers]

 theorem head_holds
    (queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
      first.packet.declaration = GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration)
    (input : first.input = last.input) (names : ∀ name, first.binder name = last.binder name) :
    first.SchemaHolds first.headSchema model ↔ last.SchemaHolds last.headSchema model := by
  have same := head_schema queries input
  have actual : ∀ entry ∈ first.headSchema.variables, entry.mode = .actual :=
    GeneralDictionaryActualSchema.schemas_actual _ _ _
  have rewriteHead (before : first.SchemaHolds first.headSchema model) :
      last.SchemaHolds last.headSchema model := by
    refine ⟨same ▸ before.1,?_⟩
    intro entry member
    have member' : entry ∈ first.headSchema.variables := same.symm ▸ member
    have mode := actual entry member'
    have result := before.2 entry member'
    simpa only [mode,ite_true,names entry.name] using result
  constructor
  · exact rewriteHead
  · intro after
    refine ⟨same.symm ▸ after.1,?_⟩
    intro entry member
    have mode := actual entry member
    have result := after.2 entry (same ▸ member)
    simpa only [mode,ite_true,names entry.name] using result

 theorem terminal_replay
    (declaration : first.packet.declaration = last.packet.declaration)
    (occurrence : first.packet.site.occurrence = last.packet.site.occurrence)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation
      first.packet.declaration = GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration)
    (input : first.input = last.input) (names : ∀ name, first.binder name = last.binder name)
    (terminal : first.packet.declaration.requirements = [])
    (old : Holds first model)
    (current : GeneralNominalState.Models last.packet.context.state model)
    (ordinary : GeneralNominalPacketSupport.Ordinary last.packet model)
    (projections : GeneralNominalRecursiveInspection.ProjectionModels last.packet.context.state
      (GeneralNominalPacketSupport.report last.packet) model)
    (fits : ∀ name, name ∈ last.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed last.packet name →
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture last.packet).inputs name)
        (model (last.binder name)).1) : Holds last model := by
  have terminal' : last.packet.declaration.requirements = [] := declaration ▸ terminal
  have outputs := (GeneralDictionaryDefaultTerminalOutputs210.outputs_iff declaration occurrence
    constructors interpretation terminal names).mp old.2.2
  refine ⟨current,⟨ordinary,projections,input ▸ old.2.1.2.2.1,fits,
    (head_holds queries input names).mp old.2.1.2.2.2.2.1,?_,?_⟩,outputs⟩
  · intro equation member _
    exact outputs equation member
  · intro clause member
    rw [terminal'] at member
    cases member
end Yulang.GeneralDictionaryDefaultActualHead210
