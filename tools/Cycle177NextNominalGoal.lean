import Yulang.GeneralNominalSharedCaptureFacts
import Yulang.GeneralDictionaryCenteredScalarIntervals177

/-! Planning artifact only. The proposition below is a proposed next lemma,
not a proof, axiom, or exported library declaration. No inhabitant is supplied. -/
namespace Cycle177NextNominalGoal
open Yulang
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection

def TerminalPairResidual (roles : Roles.RoleDecls) : Prop :=
  ∀ (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (lower upper : Fin context.state.base.slots)
    (left right : GeneralNominalState.Descriptor context.state.base.slots),
    lower ≠ upper →
    context.state.nominals lower = some left →
    context.state.nominals upper = some right →
    left.declaration.name = right.declaration.name →
    ∀ (count : Nat) (names : Fin count → Nat)
      (lowBounds highBounds : Fin count → GeneralNominalInspection.Bounds context.state),
      Function.Injective names →
      left.arguments = List.ofFn (fun i => .type (lowBounds i)) →
      right.arguments = List.ofFn (fun i => .type (highBounds i)) →
      declaration.inputNames = List.ofFn names →
      declaration.requirements = [] → root.demand.outputs = [] →
      GeneralNominalInspection.queries context.state context.interpretation declaration =
        [.nominal left.declaration.name (List.ofFn (fun i => .variables [names i]))] →
      ∀ model : GeneralNominalCommonBridge.Assignment,
        GeneralNominalState.Models context.state model →
        CommonNominalFullCarrier.Subtype
          (model (context.state.base.source lower)).1
          (model (context.state.base.source upper)).1 →
        (BranchModels registry context root declaration checked [(lower,upper)] model ↔
          PresenceNormalForm.All CommonNominalFullCarrier.model model
            (GeneralNominalAllocation.merges context.state registry root.identity declaration
              (bindings context.state (report context declaration [(lower,upper)]))))

#check TerminalPairResidual
end Cycle177NextNominalGoal
