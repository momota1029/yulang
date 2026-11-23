import Yulang.GeneralDeclarativeWitnessBareCandidates363

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessLocatedElection363
open GeneralDeclarativeWitnessBareCandidates363
  (FitsBare Decision visible decideCandidates selected_descriptor_only_of_current_visible)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

structure Chosen (e : Environment) (d : Demand) (frame : FrameKey) where
  impl : Declaration
  unique : visible e d = [impl]
  fitBare : FitsBare e d impl
  named : impl.id = frame.declaration
  actualSource : e.source.declarations[frame.sourceOrdinal]? = some impl

def choose (e : Environment) (d : Demand) (frame : FrameKey) : Option (Chosen e d frame) := do
  match ← decideCandidates e d with
  | .ambiguous .. => none
  | .selected impl all witness =>
    if authority : impl.id = frame.declaration ∧
        e.source.declarations[frame.sourceOrdinal]? = some impl then
      some ⟨impl,all,witness,authority.1,authority.2⟩
    else none

theorem election_not_called_from_compiler {e : Environment} {d : Demand} {f : FrameKey}
    (c : Chosen e d f) :
    c.impl ∈ e.source.declarations ∧ c.impl.role = d.role ∧
    ∀ other,other ∈ visible e d → other = c.impl :=
  selected_descriptor_only_of_current_visible c.unique

theorem exact_compiler_must_use_chosen_row {e : Environment} {d : Demand} {f : FrameKey}
    (c : Chosen e d f) {l} (p : GeneralDeclarativeWitnessNativePreparation360.Prepared e f d l) :
    p.impl = c.impl := Option.some.inj (p.authored.symm.trans c.actualSource)

end Yulang.GeneralDeclarativeWitnessLocatedElection363
