import Yulang.GeneralWhereVersionRecordedReuse317
import Yulang.GeneralWhereVersionStoredRow317
import Yulang.GeneralWhereVersionPreserve317
import Yulang.GeneralWhereVersionRegression317

/-! Independent exact statement checks for the original counterexample and isolated repair. -/
open Yulang
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (sourceRegistry)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionRegression317 (Accepts Evidence)

example : GeneralWhereVersionInstall317.InstallStep sourceRegistry before fixed ∧
    Accepts root dictionary ∧
    (∃ m, Models fixed m) ∧
    (∀ m, Models fixed m → Evidence m root dictionary) ∧
    ¬ B4SkeletonV8.EvidenceNode (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) :=
  GeneralWhereVersionRegression317.regression

example (prior : GeneralNominalCommonBridge.Assignment) :
    Models before prior ↔
      ∃ m, Models fixed m ∧ GeneralNominalCenteredFrame179.Agree
        (GeneralNominalVersionedJournalFrame236.sources GeneralLiveCompoundLeafInstall316.after) prior m :=
  GeneralWhereVersionPreserve317.no_legacy_model_lost_or_created prior

-- The enlarged source snapshot was reread. The certificate is for the new
-- current frame, not replaying the original capture or allocating again.
example (m : GeneralNominalCommonBridge.Assignment) (valid : Models fixed m) :
    GeneralNominalVersionedEvidence231.Frame GeneralLiveCompoundRegistry316.registry
        GeneralWhereVersionCommit317.core root GeneralLiveCompoundRegistry316.declaration.id
        GeneralWhereVersionRootReport317.plan ∧
    GeneralWhereVersionSemantics317.Holds GeneralWhereVersionRootReport317.plan m ∧
    (∀ out ∈ root.demand.outputs,
      GeneralDictionaryDefaultEvidence204.OutputWitness GeneralWhereVersionRootReport317.plan m out) ∧
    (∀ d ∈ GeneralWhereVersionCompiler317.children GeneralWhereVersionRootReport317.plan,
      GeneralNominalSaturationState.Generated GeneralWhereVersionCommit317.core.erased.current root d) :=
  GeneralWhereVersionCurrentCert317.current_certified m valid

example :
    GeneralWhereVersionCase317.occ.identity = GeneralLiveCompoundChildSite316.child.identity ∧
    GeneralWhereVersionCase317.occ ≠ GeneralLiveCompoundChildSite316.child ∧
    GeneralLiveCompoundChildSite316.child ∉
      GeneralWhereVersionCompiler317.children GeneralWhereVersionRootReport317.plan :=
  ⟨GeneralWhereVersionFrontier317.same_identity,GeneralWhereVersionLeafRegistry317.corrected_not_old,
    GeneralWhereVersionFrontier317.current_not_historical⟩

example : GeneralWhereVersionEndpointChoice317.lookup
      GeneralLiveCompoundPost316.raw GeneralWhereVersionCase317.lower = .fresh :=
  GeneralWhereVersionEndpointChoice317.first_install.1

example : GeneralWhereVersionEndpointChoice317.lookup GeneralWhereVersionSnapshot317.snap
      (GeneralVersionedEndpointAddress315.atCell GeneralWhereVersionRootReport317.plan .lower
        GeneralLiveCompoundRegistry316.otherChild.id 0 GeneralWhereVersionCase317.expr) =
      .slot GeneralWhereVersionBase317.loSlot :=
  GeneralWhereVersionEndpointChoice317.reuses.1

example (m : GeneralNominalCommonBridge.Assignment) (valid : Models fixed m) :
    GeneralWhereVersionCase317.lowerRow.Holds
      (GeneralNominalVersionedPlans231.variables GeneralWhereVersionRootReport317.plan m) m ∧
    GeneralWhereVersionCase317.upperRow.Holds
      (GeneralNominalVersionedPlans231.variables GeneralWhereVersionRootReport317.plan m) m :=
  GeneralWhereVersionRecordedReuse317.from_recorded_rows m valid
