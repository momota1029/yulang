import Yulang.GeneralSourceMetadataSites291

/-! The finite diagnostic list is exact for the already-defined coverage
fragment. Outside that fragment does not mean language rejection. -/
namespace Yulang.GeneralSourceMetadataDiagnostics291
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarations (Registry)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralSourceMetadataUse291 (UsesOK check check_exact use_append)
open GeneralSourceMetadataDefaults291 (Default Manifest coverageCheck coverage_exact)
open GeneralSourceMetadataSites291 (Entry sourceSites source_queries)
open GeneralSourceMetadataProblem291 (Problem problem empty_iff_use)

structure Failure where
  entry : Entry
  details : Problem
  deriving DecidableEq, Repr

def issues (c : Constructors) (i : Interpretation) (entries : List Entry) : List Failure :=
  entries.filterMap (fun e => (problem c i e.query).map (fun p => ⟨e,p⟩))

theorem issues_exact (c : Constructors) (i : Interpretation) (entries : List Entry) :
    issues c i entries = [] ↔ UsesOK c i (entries.map Entry.query) := by
  induction entries with
  | nil => simp [issues,UsesOK]
  | cons e rest ih =>
    simp only [issues,List.filterMap_cons] at ih ⊢
    rw [List.map_cons,GeneralSourceMetadataUse291.use_cons,← empty_iff_use,← ih]
    cases problem c i e.query <;> simp

def diagnostics (r : Registry) (i : Interpretation) (defaults : List Default) : List Failure :=
  issues r.constructors i (sourceSites r.declarations defaults)

theorem no_diagnostics_iff (r : Registry) (i : Interpretation) (defaults : List Default)
    (known : Manifest r.roles defaults) : diagnostics r i defaults = [] ↔ Coverage r i := by
  rw [diagnostics,issues_exact,source_queries,use_append,← coverage_exact _ _ _ known]
  simp only [coverageCheck,GeneralSourceMetadataDeclarations291.explicitCheck,
    GeneralSourceMetadataDefaults291.defaultCheck,Bool.and_eq_true,check_exact]

end Yulang.GeneralSourceMetadataDiagnostics291
