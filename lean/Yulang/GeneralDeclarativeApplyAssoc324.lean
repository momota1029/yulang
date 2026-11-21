import Yulang.GeneralDeclarativeNFResolve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeApplyAssoc324
open GeneralDeclarations (Checked Registry Declaration)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEntailment320 (appendFacts Holds)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNormalizeAssoc324 (one row_iff collects applied_models)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeNFNode324 (Reads BodyCoverage)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeBatch320 (collect)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDictionaryAssociatedProvenance (lookup_exact declared_covered)
open GeneralNominalCenteredHeadMatExpressions (translate_complete)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralDeclarativeSubstitution320 (logical)
open CommonRoleOutermostResolver (Frontier)

theorem exact_rows (checked : Checked r) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (requested : Declared r d) (covers : BodyCoverage r interp d impl) :
    ∃ rows, collect (one r interp impl d capture) d.outputs = some rows ∧
      ∀ row, row ∈ rows ↔ SourceEquation r interp d impl capture row := by
  have declared := (checked.2 impl visible).signature
  have nodup := (checked.2 impl visible).identified.2.2.1
  have single : ∀ out ∈ d.outputs, ∃ row, one r interp impl d capture out = some [row] := by
    intro out used
    obtain ⟨body,supplied⟩ := declared_covered r.roles impl declared out.name (role.symm ▸ requested out used)
    obtain ⟨normalized,printed⟩ := translate_complete (covers out used body supplied)
    exact ⟨⟨out.target,logical (bodyCapture d capture body) .actual normalized⟩,
      by simp [one,(lookup_exact r.roles impl nodup out.name body).mpr supplied,printed]⟩
  obtain ⟨rows,built,found⟩ := collects single
  exact ⟨rows,built,fun row => (found row).trans (row_iff checked visible).symm⟩

/-- One declarative associated-rule application, for an actual selected
source occurrence. Its result adds specified ordinary equations only;
there is no executor state or inference history in the state. -/
structure Applies (s : State) (r : Registry) (interp : Interpretation)
    (localRule : Demand → Frontier Demand → Prop) (d : Demand) (impl : Declaration)
    (names : Names) (place : Placement) (written : List Equation) : Prop where
  visible : impl ∈ r.declarations
  role : impl.role = d.role
  choice : localRule d (.selected impl.id (children impl names place))
  sourceRead : Reads s r interp d impl names place
  requestNames : Declared r d
  sourceBodies : BodyCoverage r interp d impl
  emitted : collect (one r interp impl d names.input) d.outputs = some written

theorem equations (checked : Checked r)
    (event : Applies s r interp localRule d impl names place written) :
    ∀ row, row ∈ written ↔ SourceEquation r interp d impl names.input row := by
  obtain ⟨rows,emitted,exact⟩ := exact_rows (capture := names.input) checked event.visible
    event.role event.requestNames event.sourceBodies
  cases Option.some.inj (emitted.symm.trans event.emitted)
  exact exact

theorem effect (checked : Checked r)
    (event : Applies s r interp localRule d impl names place written) (m) :
    Models (appendFacts s written) m ↔ Models s m ∧
      ∀ row, SourceEquation r interp d impl names.input row → Holds m row :=
  applied_models (equations checked event) m

theorem closure (checked : Checked r)
    (event : Applies s r interp localRule d impl names place written) :
    StableUnder (appendFacts s written) (SourceEquation r interp d impl names.input) := by
  apply stable_exact.mpr
  intro row source m valid
  exact ((effect checked event m).mp valid).2 row source

end Yulang.GeneralDeclarativeApplyAssoc324
