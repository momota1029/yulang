import Yulang.GeneralRebaseCompiledRegressions282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledEvidenceAt282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseProspective282 (Compiled decoded compile_old)
open GeneralRebaseHistoryOrder282 (decode history compatible)
open GeneralDictionaryReadback (Payload)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralNominalOrderedRaw248 (read_mapping)
open CommonRoleOutermostResolver (All₂)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {state : State roles}

def Evidence (r : Registry) (state : State roles) (base : Assignment) (focus : Occurrence roles)
    (data : Payload) :=
  GeneralNominalRebaseEvidenceView243.Evidence (registry r) state.core (mapping (history state)) base focus data

theorem evidence_exact (r : Registry) (state : State roles) (m : Assignment)
    (focus : Occurrence roles) (data : Payload) :
    Evidence r state m focus data ↔ (boundary roles).Evidence r state (decode state m) focus data := by
  unfold Evidence decode
  rw [GeneralNominalRebaseEvidenceView243.evidence_exact,read_mapping]
  rfl

theorem map₂ {α β : Type} {P Q : α → β → Prop}
    (convert : ∀ a b, P a b → Q a b) {xs : List α} {ys : List β}
    (haveAll : All₂ P xs ys) : All₂ Q xs ys := by
  induction haveAll with
  | nil => exact .nil
  | cons first rest ih => exact .cons (convert _ _ first) ih

def EvidenceAt (r : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ m, Compiled state m → ∀ focus key children dictionaries,
    (focus = root ∨ (boundary roles).Generated r state root focus) →
    (boundary roles).Stable r state focus →
    (∀ child, child ∈ children → (boundary roles).Stable r state child) →
    GeneralNominalVersionedMixedSourceBoundary234.Local r state focus (.selected key children) →
    All₂ (Evidence r state m) children dictionaries → Evidence r state m focus (.node key dictionaries)

theorem equivalent_at (reach : Reachable r root state) :
    EvidenceAt r state root ↔ B4SkeletonV8.EvidenceAt (boundary roles) r state root := by
  have empty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach
  have records := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  constructor
  · intro new a held focus key children dictionaries found stable childrenStable selected below
    have valid : Models state a := held
    have eq := compatible reach valid
    have same (c : Occurrence roles) (d : Payload) :
        (boundary roles).Evidence r state (decode state a) c d ↔ (boundary roles).Evidence r state a c d :=
      GeneralNominalRebaseEvidenceProjection243.evidence_congruent (registry r) state.core c d _ _ eq
    have translated := map₂ (fun child data e =>
      (evidence_exact r state a child data).mpr ((same child data).mpr e)) below
    have output := new a (compile_old records empty a valid) focus key children dictionaries
      found stable childrenStable selected translated
    exact (same _ _).mp ((evidence_exact r state a focus _).mp output)
  · intro old a checked focus key children dictionaries found stable childrenStable selected below
    have translated := map₂ (fun child data e => (evidence_exact r state a child data).mp e) below
    have output := old (decode state a) ((decoded empty a).mp checked) focus key children dictionaries
      found stable childrenStable selected translated
    exact (evidence_exact r state a focus _).mpr output

end Yulang.GeneralRebaseCompiledEvidenceAt282
