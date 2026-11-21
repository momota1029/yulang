import Yulang.GeneralDeclarativeNFHead324
import Yulang.GeneralDeclarativeNormalizeAssoc324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFNode324
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (appendFacts Entails conservative_append)
open GeneralDeclarativeDemand320 (Demand Bounds bounds_sound)
open GeneralDeclarativeAssembly320 (Meaning Node)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputs320 (OutputMeaning bodyPattern bodyCapture)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeAssocModel323 (actual_output)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children all_clauses)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeNFHead324 (fact reads)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNodeFacts320 (compiled_clauses)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeNormalized320 (ordered_map)
open GeneralDictionaryAssociatedProvenance (Supplies declared_covered)
open GeneralNominalCenteredHeadMatExpressions (translate translate_complete)
open GeneralNominalCenteredHeadWFSource (PatternCovered)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)

def BodyCoverage (r : Registry) (interp : Interpretation) (d : Demand) (impl : Declaration) : Prop :=
  ∀ out ∈ d.outputs, ∀ body, Supplies r.roles impl out.name body →
    PatternCovered r.constructors interp (normalize (bodyPattern body))

structure Reads (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (impl : Declaration) (names : Names) (place : Placement) : Prop where
  head : All₂ (fun arg pattern => Bounds s arg ∧ Result s (fact r.constructors interp names.input arg pattern))
    d.arguments impl.head
  captureBounds : ∀ n ∈ impl.inputNames, Bounds s (names.input n)
  coherence : Agree impl names
  clauses : ∀ clause ∈ impl.requirements,
    Ready s r interp impl clause names (place.compound clause) (place.targets clause)

theorem output_meaning {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (declared : Declared r d) (covers : BodyCoverage r interp d impl)
    (applied : StableUnder s (SourceEquation r interp d impl capture))
    (m) (valid : Models s m) (out) (requested : out ∈ d.outputs) :
    OutputMeaning r.roles r.constructors interp impl d capture m out := by
  have wanted := role.symm ▸ declared out requested
  obtain ⟨body,supplied⟩ := declared_covered r.roles impl (checked.2 impl visible).signature out.name wanted
  obtain ⟨form,found⟩ := translate_complete (covers out requested body supplied)
  have law : SourceEquation r interp d impl capture
      ⟨out.target,logical (bodyCapture d capture body) .actual form⟩ :=
    ⟨out,requested,body,supplied,form,found,rfl⟩
  exact (actual_output checked visible supplied found m).mp (stable_exact.mp applied _ law m valid)

/-- A normalized head uses only visible fields. The ordinary source
associated rules, and not availability of a raw erased translation,
supply the output equation used for recursive evidence. -/
theorem meaning {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (declared : Declared r d)
    (covers : BodyCoverage r interp d impl) (proof : Reads s r interp d impl names place)
    (applied : StableUnder s (SourceEquation r interp d impl names.input))
    (m) (valid : Models s m) :
    Meaning r interp m d impl names.input (children impl names place) := by
  obtain ⟨rows,whereCompiled,truth⟩ := all_clauses proof.coherence proof.clauses
  have extended := (conservative_append truth m).mpr valid
  refine ⟨visible,role,fun n asked => bounds_sound (proof.captureBounds n asked) m valid,?_,?_,
    output_meaning checked visible role declared covers applied m valid⟩
  · exact ordered_map proof.head (fun _ _ _ _ h => reads h.1 h.2 m valid)
  · exact compiled_clauses (s := appendFacts s rows) (checked.2 impl visible)
      proof.captureBounds whereCompiled (fun _ read => List.mem_append_right _ read) m extended

end Yulang.GeneralDeclarativeNFNode324
