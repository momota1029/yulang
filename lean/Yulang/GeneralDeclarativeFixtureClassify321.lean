import Yulang.GeneralDeclarativeFixtureGraph321
import Yulang.GeneralDeclarativeFixtureGenerate321
import Yulang.GeneralDeclarativeExampleTree320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeFixtureClassify321
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeExampleRead320 (root_only leaf_only)
open GeneralDeclarativeExampleTree320 (dictionary diagnostic)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeFixtureGraph321 (not_recursive)
open GeneralDeclarativeFixtureSupport321 (support root_ready leaf_ready probe_root probe_leaf)
open GeneralDeclarativeFixtureGenerate321 (root_generation leaf_generation)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativePriority321 (Candidates Local Recurs Blocked Survives)
open GeneralDeclarativeNormalizedLocal321 (Generates normalized_classify_sound)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Resolves Summarizes Classify Frontier)

def tested : Candidates :=
  ⟨HeadMatches (restriction support) registry.constructors interp,
    fun d decl => ¬HeadMatches (restriction support) registry.constructors interp d decl⟩

abbrev localRule := Local state registry interp support tested (Generates state support registry interp)

theorem noK2 (d) : ¬Recurs state registry interp tested d := by
  rintro (⟨arg,_,cycle⟩|⟨impl,_,i,arg,pat,code,_,_,_,site,_,cycle⟩)
  · exact not_recursive arg.lower cycle
  · exact not_recursive site cycle

theorem root_selected : localRule root (.selected wrap.id [child]) := by
  refine .selected root_ready (noK2 _) ?_ ⟨⟨List.mem_cons_self,rfl⟩,probe_root⟩ ?_ root_generation
  · rintro ⟨candidate,⟨visible,role⟩,blocked⟩
    have eq := root_only candidate visible role
    subst candidate
    exact blocked probe_root
  · intro candidate ⟨⟨visible,role⟩,_⟩
    rw [root_only candidate visible role]

theorem leaf_selected : localRule child (.selected leaf.id []) := by
  refine .selected leaf_ready (noK2 _) ?_
    ⟨⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩,probe_leaf⟩ ?_ leaf_generation
  · rintro ⟨candidate,⟨visible,role⟩,blocked⟩
    have eq := leaf_only candidate visible role
    subst candidate
    exact blocked probe_leaf
  · intro candidate ⟨⟨visible,role⟩,_⟩
    rw [leaf_only candidate visible role]

theorem resolved : Classify localRule root (.selected dictionary) :=
  ⟨diagnostic,.selected root_selected (.cons (.selected leaf_selected .nil) .nil),
    GeneralDeclarativeExampleTree320.completes⟩

/-- Both conclusions are nonvacuous. The route to the evidence is through the
support-gated classifier and normalized ordinary compiler, not a base fixture
asserting a selected root with the desired recipe. -/
theorem sound (m : Assignment) (fits : Models state m) : Evidence registry interp m root dictionary :=
  normalized_classify_sound checked m fits resolved

theorem nonvacuous : Models state model ∧ Evidence registry interp model root dictionary :=
  ⟨valid,sound model valid⟩

end Yulang.GeneralDeclarativeFixtureClassify321
