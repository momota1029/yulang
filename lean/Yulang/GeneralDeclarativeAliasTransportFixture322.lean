import Yulang.GeneralDeclarativeDemandAliases322
import Yulang.GeneralDeclarativeEmissionClassify322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasTransportFixture322
open GeneralDeclarativeExistingFixture322 (state supported model valid)
open GeneralDeclarativeExistingFixtureRead322 (whereRead namedPath)
open GeneralDeclarativeExampleSource320 (registry interp leaf checked)
open GeneralDeclarativeEmissionClassify322 (localRule child_select)
open GeneralDeclarativeEmissionLocal322 (source_sound)
open GeneralDeclarativeDemandAliases322 (Same evidence_transport)
open GeneralDeclarativeEqualities322 (entails)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

abbrev emitted := GeneralDeclarativeExampleSource320.child
abbrev aliased := GeneralDeclarativeExistingFixture322.child

theorem same_arguments_and_output (m : Assignment) (valid : Models state m) :
    Same m emitted aliased := by
  refine ⟨rfl,.cons ⟨?_,?_,?_⟩ .nil,.cons ⟨rfl,?_⟩ .nil⟩
  · exact eqv_symm (entails whereRead.1 m valid)
  · exact eqv_symm (entails whereRead.2.1 m valid)
  · exact eqv_symm (entails whereRead.2.2 m valid)
  · exact eqv_symm (entails namedPath m valid)

theorem exact_child_accepted : Classify localRule emitted (.selected (.node leaf.id [])) :=
  ⟨.selected leaf.id [],.selected child_select .nil,.selected .nil (.selected rfl)⟩

/-- Truth at the source emitter's exact positions can be transported to
the existing alias presentation in the same model. This does not identify
or replace either demand's ordinary source names. -/
theorem aliases_of_actual_child (m : Assignment) (valid : Models state m) :
    Evidence registry interp m aliased (.node leaf.id []) :=
  evidence_transport (same_arguments_and_output m valid)
    (source_sound checked m valid exact_child_accepted)

end Yulang.GeneralDeclarativeAliasTransportFixture322
