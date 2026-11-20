import Yulang.GeneralRebaseDepthPathEvidenceAt285
import Yulang.GeneralRebaseDefaultReads285
import Yulang.GeneralRebaseSourceRowRegression285
import Yulang.GeneralRebaseDisplayFrame285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12000000

namespace Yulang.Cycle285Usage

open GeneralDictionaryOutputDepth252 (registry sourceRegistry root roles model plan)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)

example :
    GeneralRebaseCoordinateProfile285.ofEquation plan Core.PresenceGeneration.CompTerm.var 3
      GeneralRebaseDepthReads285.explicit = some ⟨[3,2],[]⟩ := by
  rw [GeneralRebaseCoordinateProfile285.ofEquation_exact,GeneralRebaseDepthReads285.equation_emitted]
  rfl

example :
    GeneralRebaseCoordinateProfile285.ofEquation plan GeneralRebaseSourceRowRegression285.mapping 3
      GeneralRebaseDepthReads285.explicit = some ⟨[3],[7]⟩ :=
  GeneralRebaseSourceRowRegression285.coordinate_separation

example :
    GeneralRebaseCoordinateProfile285.ofEquation GeneralDictionaryDefaultGap206Source.plan
      Core.PresenceGeneration.CompTerm.var 0 GeneralRebaseDefaultReads285.default = some ⟨[0,1],[]⟩ :=
  GeneralRebaseDefaultReads285.coordinates

example : ¬ GeneralRebaseDepthMinimal285.Frames (Models installed) [0,1,2] := by
  intro framed
  have impossible := (GeneralRebaseDepthMinimal285.minimal_raw _).mp framed 3 (by decide)
  exact (by decide : 3 ∉ ([0,1,2] : List Nat)) impossible

example : GeneralRebaseDepthMinimal285.Frames GeneralRebaseDepthMinimal285.Canonical [0,1,2] := by
  apply (GeneralRebaseDepthMinimal285.minimal_canonical _).mpr
  intro n small
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide

example : ActualPath installed refreshed 2 := GeneralRebaseDepthPathSharp285.two_refreshes

example {last : State roles} (notPossible : ActualPath installed last 3) : False :=
  (by decide : ¬ (3 : Nat) ≤ 2) (GeneralRebaseDepthPathRank285.all_after_install notPossible).1

example {last : State roles} {n : Nat} (actual : ActualPath installed last n) :
    Models last model ∧ Evidence registry last.core model root (.node 0 []) := by
  refine (GeneralRebaseDepthPathEvidence285.query actual model _).mpr ⟨installed_model,?_⟩
  exact (GeneralRebaseDepthPayload285.evidence_exact model installed_model _).mpr rfl

example {last : State roles} {n : Nat} (actual : ActualPath installed last n) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
      sourceRegistry last root :=
  GeneralRebaseDepthPathEvidenceAt285.evidence_at actual

example : GeneralRebaseDepthMinimal285.Frames
    (fun m => Models GeneralRebaseCompiledDisplay277.after m ∧
      Evidence GeneralRebaseCompiledDisplay277.compiled GeneralRebaseCompiledDisplay277.after.core
        m GeneralNominalExamples.displayRoot (.node 1 [.node 3 []])) [0,1] :=
  GeneralRebaseDisplayFrame285.parent_finite _

end Yulang.Cycle285Usage

#print axioms Yulang.GeneralRebaseDepthPathEvidenceAt285.move_location
#print axioms Yulang.GeneralRebaseDepthPathEvidenceAt285.kept_survivor
#print axioms Yulang.GeneralRebaseDepthPathEvidenceAt285.selected_unique
#print axioms Yulang.GeneralRebaseDepthPathEvidenceAt285.evidence_at
