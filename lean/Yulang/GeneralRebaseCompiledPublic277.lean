import Yulang.GeneralRebaseCompiledPayload277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseCompiledPublic277
open GeneralNominalExamples (state base heads listDescriptor registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralRebaseCompiledInstall277 (models direct_models)
open GeneralRebaseDisplayExecutor276 (Goal invocation)
open GeneralRebaseDisplayPayload276 (accepts)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_refl)
open GeneralNominalState (FitsAll)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open GeneralDictionaryReadback (Payload)

abbrev Public := Ty × Ty

def project (m : Assignment) : Public := ((m 0).1,(m 1).1)

def decode (p : Public) : Assignment :=
  fun id => (if id = 0 then p.1 else if id = 1 then p.2 else .bottom,Common.rowEmpty)

def Model (p : Public) : Prop :=
  Equivalent p.2 (.base .int) ∧
  ∃ arg : Ty, Equivalent p.2 arg ∧ Equivalent p.1 (CommonNominalFullCarrier.nominal 0 [.inl arg])

theorem project_decode (p : Public) : project (decode p) = p := by
  cases p
  rfl

theorem read_source (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
    Model (project m) := by
  have scalar := valid.1.2.1 (1 : Fin 2) (.base .int) rfl
  obtain ⟨args,fit,denotes⟩ := valid.2.1 (0 : Fin 2) listDescriptor rfl
  change FitsAll (base true) m [.type (1,1)] args at fit
  cases fit with
  | cons first tail =>
    cases tail
    rename_i value
    cases value with
    | inl ty =>
      exact ⟨scalar,ty,first,denotes⟩
    | inr row => cases first

theorem write_source (m : Assignment) (valid : Model (project m)) :
    GeneralNominalState.Models (state true) m := by
  obtain ⟨int,ty,fit,denotes⟩ := valid
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact int.1
    · exact int.2
  · intro slot term recorded
    change (heads true slot).equation = some term at recorded
    by_cases one : slot = 1
    · subst slot
      have equal : term = .base .int := (Option.some.inj recorded).symm
      subst term
      exact int
    · simp [heads,one,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [base,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot
      have equal : listDescriptor = descriptor := Option.some.inj recorded
      subst descriptor
      exact ⟨[.inl ty],.cons fit .nil,denotes⟩
    · simp [zero] at recorded

theorem full_exact (m : Assignment) : Models after m ↔ Model (project m) :=
  (models m).trans ((GeneralRebaseDisplayExecutor276.model_exact .source m).trans
    ⟨read_source m,write_source m⟩)

theorem canonical_exact (p : Public) : Models after (decode p) ↔ Model p := by
  rw [full_exact,project_decode]

theorem repository_projection (p : Public) : (∃ m, project m = p ∧ Models after m) ↔ Model p := by
  constructor
  · rintro ⟨m,rfl,valid⟩
    exact (full_exact m).mp valid
  · intro valid
    exact ⟨decode p,project_decode p,(canonical_exact p).mpr valid⟩

theorem public_evidence (goal : Goal) (p : Public) (data : Payload) :
    (Model p ∧ accepts goal data = true) ↔
    (∃ m, project m = p ∧ Models after m ∧
      (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Evidence
        registry after m (invocation goal) data) := by
  constructor
  · rintro ⟨valid,accepted⟩
    have full := (canonical_exact p).mpr valid
    exact ⟨decode p,project_decode p,full,
      (GeneralRebaseCompiledPayload277.adapter_exact goal _ full data).mp accepted⟩
  · rintro ⟨m,rfl,full,actual⟩
    exact ⟨(full_exact m).mp full,
      (GeneralRebaseCompiledPayload277.adapter_exact goal _ full data).mpr actual⟩

end Yulang.GeneralRebaseCompiledPublic277
