import Yulang.GeneralDeclarativeNFEmit324
import Yulang.GeneralDeclarativeApplyAssoc324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFComplete324
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds bounds_sound)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeEntailment320 (appendFacts Entails literal conservative_append)
open GeneralDeclarativeNFHead324 (fact reads)
open GeneralDeclarativeNFWhere324 (clauseFacts clauses_sound)
open GeneralDeclarativeNFEmit324 (Read old_implies ordinary_forest)
open GeneralDeclarativeNFNode324 (BodyCoverage output_meaning)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeApplyAssoc324 (exact_rows)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact stable_batch)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeBatch320 (zipFacts collect)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeNormalized320 (ordered_map)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

/-- The old ordinary node compiler required interpretations of erased
constructors. All three components here use the source normal form. -/
def facts (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (impl : Declaration) (d : Demand) (kids : List Demand) : Option (List Equation) :=
  if impl.role = d.role then do
    let head ← zipFacts (fact r.constructors interp capture) d.arguments impl.head
    let clauses ← zipFacts (clauseFacts r interp capture) impl.requirements kids
    let outputs ← collect (one r interp impl d capture) d.outputs
    pure (head ++ clauses ++ outputs)
  else none

structure ReadBack (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (impl : Declaration) (names : Names) (place : Placement) : Prop where
  head : All₂ (fun arg pat => Bounds s arg ∧ Result s (fact r.constructors interp names.input arg pat))
    d.arguments impl.head
  bounds : ∀ binder ∈ impl.inputNames, Bounds s (names.input binder)
  coherent : Agree impl names
  whereRead : ∀ clause ∈ impl.requirements,
    Read s r interp impl clause names (place.compound clause) (place.targets clause)

theorem old_port {s : State} (stable : GeneralDeclarativeNFNode324.Reads s r interp d impl names place) :
    ReadBack s r interp d impl names place :=
  ⟨stable.head,stable.captureBounds,stable.coherence,fun clause has => old_implies (stable.clauses clause has)⟩

theorem produces {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (declared : Declared r d)
    (cover : BodyCoverage r interp d impl) (obs : ReadBack s r interp d impl names place)
    (stable : StableUnder s (SourceEquation r interp d impl names.input)) :
    Result s (facts r interp names.input impl d (children impl names place)) := by
  obtain ⟨h,hd,hv⟩ := zip_result
    (ordered_map obs.head (fun _ _ _ _ fact => fact.2))
  obtain ⟨w,ws,wv⟩ := ordinary_forest obs.coherent obs.whereRead
  obtain ⟨o,forms,emitted⟩ := exact_rows (capture := names.input) checked visible role declared cover
  refine ⟨h++w++o,by simp [facts,role,hd,ws,forms],?_⟩
  intro row found
  rcases List.mem_append.mp found with before|output
  · exact (List.mem_append.mp before).elim (hv row) (wv row)
  · exact stable_exact.mp stable row ((emitted row).mp output)

theorem local_sound {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (declared : Declared r d)
    (cover : BodyCoverage r interp d impl) (obs : ReadBack s r interp d impl names place)
    (stable : StableUnder s (SourceEquation r interp d impl names.input)) (m) (valid : Models s m) :
    Meaning r interp m d impl names.input (children impl names place) := by
  obtain ⟨rows,wrote,truth⟩ := ordinary_forest obs.coherent obs.whereRead
  refine ⟨visible,role,fun n used => bounds_sound (obs.bounds n used) m valid,?_,?_,
    output_meaning checked visible role declared cover stable m valid⟩
  · exact ordered_map obs.head (fun _ _ _ _ rv => reads rv.1 rv.2 m valid)
  · exact clauses_sound (s := appendFacts s rows) (checked.2 impl visible)
      obs.bounds wrote (fun _ h => List.mem_append_right _ h) m ((conservative_append truth m).mpr valid)

end Yulang.GeneralDeclarativeNFComplete324
