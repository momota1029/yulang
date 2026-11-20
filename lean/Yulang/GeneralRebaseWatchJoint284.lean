import Yulang.GeneralRebaseActualWatch284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchJoint284
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseActualWatch284 (Cache interpret preserve_models preserve_evidence)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseSliceEvidence283 (reads Evidence full)
open GeneralRebaseHistoryOrder282 (decode)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseWholeJournal282 (View exact_view)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

def Query (watch : List Nat) (state : State roles) (r : Registry) (a : Assignment)
    (focus : Occurrence roles) (data : Payload) : Prop :=
  Models state a ∧ ∃ family : List (Plan roles), reads family ⊆ watch ∧ Evidence family r state a focus data

def Complete (watch : List Nat) (state : State roles) (r : Registry) (focus : Occurrence roles)
    (data : Payload) : Prop :=
  ∀ a : Assignment, Joint state r focus data (decode state a) →
    ∃ family : List (Plan roles), reads family ⊆ watch ∧ Evidence family r state (decode state a) focus data

variable {roles : Roles.RoleDecls} {state : State roles} {registry : Registry} {root : Occurrence roles}
  {watch : List Nat} {defs : List (GeneralPresenceDefinitionRewrite244.Entry Nat)}

theorem query (valid : Cache state watch defs) (recorded : Recorded state)
    (empty : LegacyEmpty state) (journalOnly : journalReads state ⊆ watch)
    (r : Registry) (base : Assignment) (focus : Occurrence roles) (data : Payload) :
    Query watch state r (interpret defs base) focus data ↔
      Query watch state r (decode state base) focus data := by
  unfold Query
  exact and_congr (preserve_models valid recorded empty journalOnly base) <|
    exists_congr (fun family => and_congr_right (fun covered =>
      preserve_evidence valid recorded r family covered base focus data))

theorem certified (valid : Cache state watch defs) (seen : Reachable registry root state)
    (journalOnly : journalReads state ⊆ watch) (r : Registry) (base : Assignment)
    (focus : Occurrence roles) (data : Payload)
    (finiteComplete : Complete watch state r focus data) :
    Query watch state r (interpret defs base) focus data ↔ View state r focus data base := by
  rw [query valid (GeneralNominalVersionedMixedSeedLedger237.reachable seen)
    (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty seen) journalOnly, exact_view seen]
  constructor
  · rintro ⟨models,family,_,evidence⟩
    exact ⟨models,(full r state _ focus data).mpr ⟨family,evidence⟩⟩
  · intro both
    exact ⟨both.1,finiteComplete base both⟩

theorem never_false (valid : Cache state watch defs) (seen : Reachable registry root state)
    (journalOnly : journalReads state ⊆ watch) (r : Registry) (base : Assignment)
    (focus : Occurrence roles) (data : Payload) :
    Query watch state r (interpret defs base) focus data → View state r focus data base := by
  rw [query valid (GeneralNominalVersionedMixedSeedLedger237.reachable seen)
    (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty seen) journalOnly, exact_view seen]
  rintro ⟨models,family,_,evidence⟩
  exact ⟨models,(full r state _ focus data).mpr ⟨family,evidence⟩⟩

end Yulang.GeneralRebaseWatchJoint284
