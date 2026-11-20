import Yulang.GeneralGeneratedDisplayObserved299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedDisplayPhase299
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (after compiled frame_parent)
open GeneralRebaseDisplayFrame276 (before)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedEvidence231 (Evidence Frame Instance)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralGeneratedDisplayTable299 (table decode)
open GeneralGeneratedDictionaryScope299 (InScope Faithful all_left)
open GeneralGeneratedMixedCurrentNodes299 (Providers)
open CommonRoleOutermostResolver (All₂)
open B4Target (Steps)
open B4TargetV8

abbrev Route (s : State roles) : Prop :=
  Steps ((boundary roles).Step registry displayRoot) before s

def Authorized (s : State roles) : Prop :=
    InScope (boundary roles) registry s displayRoot table decode ∧
      Faithful (b:=boundary roles) (r:=registry) (s:=s) table decode ∧ Providers registry s table decode

theorem child_not_generated :
    ¬ GeneralNominalSaturationState.Generated before.core.erased.current displayRoot displayChild := by
  intro path
  exact GeneralRebaseCompiledEndpoint277.root_distinct (GeneralRebaseCompiledAcc277.initial_generated path).symm

theorem before_not_authorized : ¬ Authorized before := by
  intro h
  have found := (h.1 1 ⟨3,[]⟩ rfl).1
  rcases found with eq | actual
  · exact GeneralRebaseCompiledEndpoint277.root_distinct eq.symm
  · exact child_not_generated actual

theorem after_authorized : Authorized after :=
  ⟨GeneralGeneratedDisplayTable299.in_scope,GeneralGeneratedDisplayTable299.faithful,
    GeneralGeneratedDisplayBothCurrent299.providers⟩

theorem exact_authorization (s : State roles) (route : Route s) :
    Authorized s ↔ s = after := by
  rcases GeneralRebaseCompiledAcc277.exact_reached s route with rfl|rfl
  · exact ⟨fun h => False.elim (before_not_authorized h),fun eq =>
      False.elim (GeneralRebaseCompiledExecutor277.distinct eq)⟩
  · exact ⟨fun _ => rfl,fun _ => after_authorized⟩

theorem initial_child_no_evidence (m : Assignment) (p : Payload) :
    ¬ (boundary roles).Evidence registry before m displayChild p := by
  intro got
  have found : PayloadEvidence (Instance compiled before.core m) displayChild p :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr got
  cases found with
  | node rule _ =>
    obtain ⟨plan,cert⟩ := rule
    have raw : plan.packet.site = GeneralNominalDemandMerging.pointSite
        (GeneralNominalVersionedCandidates231.inputs displayRoot) :=
      List.mem_singleton.mp cert.frame.raw_recorded
    have equal : displayRoot = displayChild := by
      rw [← cert.frame.occurrence_eq,raw]
      rfl
    exact GeneralRebaseCompiledEndpoint277.root_distinct equal

theorem initial_parent_no_evidence (m : Assignment) (p : Payload) :
    ¬ (boundary roles).Evidence registry before m displayRoot p := by
  intro got
  have found : PayloadEvidence (Instance compiled before.core m) displayRoot p :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr got
  cases found with
  | node rule children =>
    obtain ⟨plan,cert⟩ := rule
    have matched := GeneralRebaseScopedFrame276.same_frame cert.frame frame_parent
      (GeneralRebaseCompiledInstall277.frame_decl cert.frame)
      (List.mem_singleton.mp cert.frame.raw_recorded)
      (List.mem_singleton.mp cert.frame.center_recorded)
    subst plan
    have nexts := cert.children_eq.trans GeneralRebaseCompiledDisplay277.children
    rw [nexts] at children
    obtain ⟨d,proof⟩ := all_left children displayChild (List.mem_singleton_self _)
    apply initial_child_no_evidence m d
    exact (GeneralDictionaryReadback.payload_iff_erased _ _ _).mp proof

theorem genuine_phase_change :
    (boundary roles).Step registry displayRoot before after ∧
      (∀ m, Models after m ↔ Models before m) ∧
      (∀ m p, ¬ (boundary roles).Evidence registry before m displayRoot p) ∧
      ∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) :=
  ⟨GeneralRebaseCompiledInstall277.adapter_step,GeneralRebaseCompiledInstall277.models,
    initial_parent_no_evidence,GeneralGeneratedDisplayBothCurrent299.root_from_current⟩

end Yulang.GeneralGeneratedDisplayPhase299
