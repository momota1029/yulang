import Yulang.GeneralRebaseDefaultFeedback284
import Yulang.GeneralRebaseCompiledPayload277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchedEvidenceAt284
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseActualWatch284 (Cache interpret preserve_evidence preserve_models)
open GeneralRebaseHistoryOrder282 (decode compatible)
open GeneralRebaseWatchJoint284 (Complete)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseSliceEvidence283 (Evidence reads full)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {state : State roles} {watch : List Nat} {defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat)}

def Admissible (watch : List Nat) (r : Registry) (state : State roles) (a : Assignment)
    (focus : Occurrence roles) (data : Payload) : Prop :=
  ∃ family : List (Plan roles), reads family ⊆ watch ∧ Evidence family (registry r) state a focus data

def InScope (r : Registry) (state : State roles) (root focus : Occurrence roles) : Prop :=
  focus = root ∨ (boundary roles).Generated r state root focus

def Coverage (watch : List Nat) (r : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  (∀ focus data, InScope r state root focus → Complete watch state (registry r) focus data) ∧
  ∀ focus key children, InScope r state root focus → Local r state focus (.selected key children) →
    ∀ child ∈ children, InScope r state root child

def CheckedEvidenceAt (watch : List Nat) (defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat))
    (r : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ a : Assignment, Models state (interpret defs a) → ∀ focus key children dictionaries,
    InScope r state root focus →
    (boundary roles).Stable r state focus →
    (∀ child, child ∈ children → (boundary roles).Stable r state child) →
    Local r state focus (.selected key children) →
    All₂ (Admissible watch r state (interpret defs a)) children dictionaries →
    Admissible watch r state (interpret defs a) focus (.node key dictionaries)

theorem admit_exact (valid : Cache state watch defs) (reach : Reachable r root state)
    (a : Assignment) (focus : Occurrence roles) (data : Payload)
    (required : Complete watch state (registry r) focus data)
    (held : Models state (decode state a)) :
    Admissible watch r state (interpret defs a) focus data ↔
      (boundary roles).Evidence r state (decode state a) focus data := by
  have records := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  constructor
  · rintro ⟨family,reads,good⟩
    exact (full (registry r) state _ focus data).mpr
      ⟨family,(preserve_evidence valid records (registry r) family reads a focus data).mp good⟩
  · intro cert
    obtain ⟨family,reads,good⟩ := required a ⟨held,cert⟩
    exact ⟨family,reads,(preserve_evidence valid records (registry r) family reads a focus data).mpr good⟩

theorem map_in_scope {P Q : Occurrence roles → Payload → Prop}
    {children : List (Occurrence roles)} {dictionaries : List Payload}
    (proof : All₂ P children dictionaries)
    (move : ∀ c ∈ children, ∀ d, P c d → Q c d) : All₂ Q children dictionaries := by
  induction proof with
  | nil => exact .nil
  | cons head rest ih =>
    exact .cons (move _ List.mem_cons_self _ head)
      (ih (fun c found d evidence => move c (List.mem_cons_of_mem _ found) d evidence))

theorem equivalent_at (valid : Cache state watch defs) (seen : Reachable r root state)
    (reads : journalReads state ⊆ watch) (covered : Coverage watch r state root) :
    CheckedEvidenceAt watch defs r state root ↔ B4SkeletonV8.EvidenceAt (boundary roles) r state root := by
  have records := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  have emp := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty seen
  have eqM (a : Assignment) := preserve_models valid records emp reads a
  constructor
  · intro checked a held focus key children dictionaries inScopeHere stable descendants selected supplied
    have rawHeld : Models state a := held
    have equal := compatible seen rawHeld
    have still := (GeneralNominalVersionedSourceCongruence238.source_models_iff equal seen).mpr rawHeld
    have eqE (f : Occurrence roles) (d : Payload) :
        (boundary roles).Evidence r state (decode state a) f d ↔ (boundary roles).Evidence r state a f d :=
      GeneralNominalRebaseEvidenceProjection243.evidence_congruent (registry r) state.core f d _ _ equal
    have localReady (f : Occurrence roles) (d : Payload) (inScope : InScope r state root f) :=
      admit_exact valid seen a f d (covered.1 f d inScope) still
    have watched := map_in_scope supplied (fun c child d e =>
      (localReady c d (covered.2 focus key children inScopeHere selected c child)).mpr ((eqE c d).mpr e))
    have result := checked a ((eqM a).mpr still) focus key children dictionaries inScopeHere stable descendants selected watched
    exact (eqE _ _).mp ((localReady _ _ inScopeHere).mp result)
  · intro statement a held focus key children dictionaries inScopeHere stable descendants selected supplied
    have still := (eqM a).mp held
    have localReady (f : Occurrence roles) (d : Payload) (inScope : InScope r state root f) :=
      admit_exact valid seen a f d (covered.1 f d inScope) still
    have raw := map_in_scope supplied (fun c child d e =>
      (localReady c d (covered.2 focus key children inScopeHere selected c child)).mp e)
    have goal := statement (decode state a) still focus key children dictionaries inScopeHere stable descendants selected raw
    exact (localReady _ _ inScopeHere).mpr goal

end Yulang.GeneralRebaseWatchedEvidenceAt284
