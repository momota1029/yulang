import Yulang.GeneralDeclarativeAppliedClause327
import Yulang.GeneralDeclarativeEvidenceFold325
import Yulang.GeneralDeclarativeProjectedFrame326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInPlace327
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeFrameReadback325 (sourceNames clause ClauseFrame)
open GeneralDeclarativeClauseBatch327 (prepare past_origin)
open GeneralDeclarativeClausePlacement327 (placement checked_inputs)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeProducedNames325 (exact_input coherent)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeNFComplete324 (ReadBack)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonRoleOutermostResolver (All₂)

theorem clause_here {s t current : State} (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations)
    (generated : prepare r.constructors i protect (sourceNames impl (targetsOnly targets) cap).input
      s impl.requirements = some (t,ports))
    (grows : Extends t current)
    (outputs : whole r i impl (sourceNames impl (placement impl.requirements ports targets) cap) targets =
      some rows)
    (present : rows ⊆ current.equations)
    (used : cl ∈ impl.requirements) :
    let place := placement impl.requirements ports targets
    ClauseFrame current r i impl cl (sourceNames impl place cap) place := by
  dsimp
  obtain ⟨port,_,known,placed⟩ := checked_inputs (targets := targets) (checked.2 impl visible) generated used
  constructor
  · refine ⟨port.code,known.1,?_⟩
    intro j p e source decoded notBare
    rw [placed]
    obtain ⟨_,lo,mid,hi⟩ := known.2 j p e source decoded notBare
    exact ⟨past_origin grows lo,past_origin grows mid,past_origin grows hi⟩
  · intro eq belongs
    obtain ⟨written,supplied⟩ := GeneralNominalCenteredHeadMatExpressions.translate_complete
      (GeneralDeclarativeNormalizeCovered322.normalize_covered
        (((coverage.1 impl visible).2.1 cl used).2 eq belongs))
    refine ⟨written,supplied,fun nonDirect => GeneralDeclarativeClauseOrigins325.origin_here ?_⟩
    exact present ((GeneralDeclarativeWhereOutputBatch327.exact outputs _).mpr
      ⟨cl,used,eq,belongs,nonDirect,written,supplied,rfl⟩)

/-- Once the *independently computed* clause payloads and associated
rows are actually present, readback and Compiles are proved in the
original arbitrary current state. No fresh-output equation is being
assumed true or silently installed. The checked ordinary head and
the identification of the compilation with the actual selected
source node are still independent obligations. -/
theorem current_sound {s t current : State} (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (generated : prepare r.constructors i protect (sourceNames impl (targetsOnly targets) cap).input
      s impl.requirements = some (t,ports))
    (grows : Extends t current)
    (whereRows : whole r i impl (sourceNames impl (placement impl.requirements ports targets) cap) targets =
      some wr)
    (ordinaryWhere : wr ⊆ current.equations)
    (rootRows : collect (one r i impl d (sourceNames impl (placement impl.requirements ports targets) cap).input)
      d.outputs = some rs)
    (ordinaryRoot : rs ⊆ current.equations)
    (captures : ∀ n ∈ impl.inputNames, Bounds current (cap n))
    (head : All₂ (fun a p => Bounds current a ∧ Result current
      (fact r.constructors i (sourceNames impl (placement impl.requirements ports targets) cap).input a p))
       d.arguments impl.head) :
    let place := placement impl.requirements ports targets
    let names := sourceNames impl place cap
    Result current (GeneralDeclarativeNFComplete324.facts r i names.input impl d (children impl names place)) ∧
    ∀ m, Models current m → Meaning r i m d impl names.input (children impl names place) := by
  let place := placement impl.requirements ports targets
  let names := sourceNames impl place cap
  have readback : ReadBack current r i d impl names place := by
    refine ⟨head,?_,coherent _ _ _,fun cl used => clause
      (clause_here checked coverage visible generated grows whereRows ordinaryWhere used)⟩
    intro n used
    unfold names sourceNames
    rw [exact_input (checked.2 impl visible) used]
    exact captures n used
  obtain ⟨covers,stable⟩ := GeneralDeclarativeAppliedSource325.stable_after_written checked visible rootRows ordinaryRoot
  exact ⟨GeneralDeclarativeNFComplete324.produces checked visible role wanted covers readback stable,
    fun m valid => GeneralDeclarativeNFComplete324.local_sound checked visible role wanted covers readback stable m valid⟩

end Yulang.GeneralDeclarativeInPlace327
