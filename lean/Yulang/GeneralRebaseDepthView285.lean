import Yulang.GeneralRebaseDepthMinimal285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDepthView285
open GeneralDictionaryOutputDepth252 (snapshot registry root initial)
open GeneralDictionaryOutputDepthInstall252 (installed step)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck final_check)
open GeneralRebaseDepthPublic285 (SourceTypes project basic inflate preserve_literal_source)
open GeneralRebaseDepthPayload285 (same_assignment_exact canonical_exact)

def projected (types : SourceTypes) (p : Payload) : Prop :=
    ∃ m : Assignment, project m = types ∧ Models installed m ∧ Evidence registry installed.core m root p

theorem projected_exact (types : SourceTypes) (p : Payload) :
    projected types p ↔ InitialTypeCheck (basic types (fun _ => Common.rowEmpty)) ∧ p = .node 0 [] := by
  constructor
  · rintro ⟨m,equal,holds,ev⟩
    have result := (same_assignment_exact m p).mp ⟨holds,ev⟩
    rw [← equal]
    exact ⟨result.1.1,result.2⟩
  · rintro ⟨has,rfl⟩
    let raw := basic types (fun _ => Common.rowEmpty)
    have equal : project raw = types := by cases types; rfl
    obtain ⟨models,evidence⟩ := (canonical_exact raw (.node 0 [])).mpr ⟨has,rfl⟩
    exact ⟨inflate (project raw) (fun n => (raw n).2),
      (preserve_literal_source _ _).trans equal,models,evidence⟩

theorem arbitrary_rows (types : SourceTypes) (p : Payload) (rows : Nat → Common.Row) :
    projected types p ↔
      Models installed (inflate types rows) ∧ Evidence registry installed.core (inflate types rows) root p := by
  let raw := basic types rows
  have equal : project raw = types := by cases types; rfl
  have field : (fun n => (raw n).2) = rows := rfl
  have h := canonical_exact raw p
  rw [equal,field] at h
  exact (projected_exact types p).trans h.symm

theorem project_raw_compat (m : Assignment) (p : Payload)
    (valid : Models installed m ∧ Evidence registry installed.core m root p) :
    projected (project m) p ∧
    Models installed (inflate (project m) (fun n => (m n).2)) ∧
      Evidence registry installed.core (inflate (project m) (fun n => (m n).2)) root p := by
  have view : projected (project m) p := ⟨m,rfl,valid⟩
  exact ⟨view,(arbitrary_rows (project m) p _).mp view⟩

theorem source_installed_common (m : Assignment) (p : Payload) :
    Models initial m ∧ p = .node 0 [] ↔ projected (project m) p := by
  rw [projected_exact]
  apply and_congr ?_ Iff.rfl
  constructor
  · intro valid
    exact (GeneralRebaseDepthGroundModels285.source_inputs m).mp
      ((GeneralNominalVersionedJournal232.initial_models _ _ _).mp valid).1
  · intro check
    exact (GeneralNominalVersionedJournal232.initial_models _ _ _).mpr
      ⟨(GeneralRebaseDepthGroundModels285.source_inputs m).mpr check,
        GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

end Yulang.GeneralRebaseDepthView285
