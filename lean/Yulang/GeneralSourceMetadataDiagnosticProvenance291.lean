import Yulang.GeneralSourceMetadataRolePermutation291

/-! Sound and complete individual diagnostic provenance. Labels are tied
to actual resolved syntax sites, not to just any key in the catalogue. -/
namespace Yulang.GeneralSourceMetadataDiagnosticProvenance291
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarations (Registry)
open GeneralNominalCenteredHeadWFSource (ConstructorUse)
open GeneralSourceMetadataSites291 (Entry sourceSites)
open GeneralSourceMetadataDiagnostics291 (Failure issues diagnostics)
open GeneralSourceMetadataDefaults291 (Default)
open GeneralSourceMetadataProblem291 (problem empty_iff_use)

theorem issue_exact (c : Constructors) (i : Interpretation) (entries : List Entry) (f : Failure) :
    f ∈ issues c i entries ↔ f.entry ∈ entries ∧ problem c i f.entry.query = some f.details := by
  unfold issues
  constructor
  · intro present
    obtain ⟨e,belong,emitted⟩ := List.mem_filterMap.mp present
    cases reason : problem c i e.query with
    | none =>
      rw [reason] at emitted
      cases emitted
    | some p =>
      rw [reason] at emitted
      cases Option.some.inj emitted
      exact ⟨belong,reason⟩
  · rintro ⟨recorded,why⟩
    exact List.mem_filterMap.mpr ⟨f.entry,recorded,by rw [why]; cases f; rfl⟩

theorem exact_origin (r : Registry) (i : Interpretation) (ds : List Default) (f : Failure) :
    f ∈ diagnostics r i ds ↔ f.entry ∈ sourceSites r.declarations ds ∧
      problem r.constructors i f.entry.query = some f.details :=
  issue_exact _ _ _ _

theorem sound_failure (r : Registry) (i : Interpretation) (ds : List Default) (f : Failure)
    (seen : f ∈ diagnostics r i ds) : ¬ ConstructorUse r.constructors i f.entry.query.1 f.entry.query.2 := by
  intro ok
  have cannot := (empty_iff_use _ _ _).mpr ok
  rw [(exact_origin _ _ _ _).mp seen |>.2] at cannot
  cases cannot

theorem complete_failure (r : Registry) (i : Interpretation) (ds : List Default) (e : Entry)
    (source : e ∈ sourceSites r.declarations ds)
    (unsupported : ¬ ConstructorUse r.constructors i e.query.1 e.query.2) :
    ∃ f ∈ diagnostics r i ds, f.entry = e := by
  cases why : problem r.constructors i e.query with
  | none => exact (unsupported ((empty_iff_use ..).mp why)).elim
  | some detail =>
    exact ⟨⟨e,detail⟩,(exact_origin ..).mpr ⟨source,why⟩,rfl⟩

end Yulang.GeneralSourceMetadataDiagnosticProvenance291
