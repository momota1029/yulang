import Yulang.GeneralRebaseHistorySupport282
import Yulang.GeneralNominalOrderedJournalClosed249

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWholeJournal282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebaseHistoryOrder282 (history decode ordered preserves_joint member_exact)
open GeneralRebaseHistorySupport282 (packet_context)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebasePrivateStore282 (Joint Public)
open GeneralRebasePortProjection280 (Project)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOrderedBlock247 (solve_outside)
open GeneralNominalRebaseJournalView243 (compile)
open GeneralNominalJournalSupport249 (support)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralNominalOrderedRaw248 (read_mapping)
open GeneralDictionaryReadback (Payload)
open GeneralPresenceDefinitionRewrite244 (Entry)
open CommonNominalFullCarrier (model)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

noncomputable def View (state : State roles) (r : Registry) (focus : Occurrence roles)
    (payload : Payload) (base : Assignment) : Prop :=
  (compile state (mapping (history state))).Models base ∧
    GeneralNominalRebaseEvidenceView243.Evidence r state.core (mapping (history state)) base focus payload

theorem exact_view (reach : Reachable registry root state) (r : Registry) (focus : Occurrence roles)
    (data : Payload) (base : Assignment) :
    View state r focus data base ↔ Joint state r focus data (decode state base) := by
  unfold View Joint
  rw [GeneralNominalRebaseJournalView243.source_exact reach,
    GeneralNominalRebaseEvidenceView243.evidence_exact,read_mapping]
  rfl

def Observable (state : State roles) (names : List Nat) : Prop :=
  ∀ id ∈ names, ∀ e ∈ history state, e.1 ≠ id

theorem preserves_reads (allowed : Observable state names) (base : Assignment) :
    GeneralNominalCenteredFrame179.Agree names (decode state base) base :=
  fun id used => solve_outside model (history state) base id (allowed id used)

theorem source_visibility (reach : Reachable registry root state)
    (names : List Nat) (initialNames : ∀ id ∈ names, id ≤ (raw state).seed) :
    Observable state names ∧ Public (raw state).seed names := by
  constructor
  · intro id listed entry provided
    obtain ⟨q,qMem,eMem⟩ := List.mem_flatMap.mp ((member_exact reach entry).mp provided)
    obtain ⟨prior,path,ctx,seed⟩ := packet_context reach q qMem
    have same := (congrArg GeneralNominalState.State.seed ctx).trans seed
    have big : (raw state).seed < entry.1 := by
      rw [← same]
      obtain ⟨name,_,_,rfl | rfl⟩ := (member_iff ..).mp eMem
      · exact GeneralNominalAggregateVersion231.above_seed ..
      · exact GeneralNominalAggregateVersion231.above_seed ..
    exact fun co => Nat.not_lt_of_ge (initialNames id listed) (co ▸ big)
  · intro id listed hidden
    obtain ⟨owner,decl,tag,rfl⟩ := hidden
    exact Nat.not_lt_of_ge (initialNames _ listed) (GeneralNominalIdentities.source_above_seed _ _)

theorem preserved_projection (reach : Reachable registry root state) (r : Registry) (focus : Occurrence roles)
    (data : Payload) (allowed : Observable state names) (outer : Assignment) :
    Project names (View state r focus data) outer ↔ Project names (Joint state r focus data) outer := by
  constructor
  · rintro ⟨base,agrees,compiled⟩
    exact ⟨decode state base,fun id seen => (preserves_reads allowed base id seen).trans (agrees id seen),
      (exact_view reach r focus data base).mp compiled⟩
  · rintro ⟨base,agrees,valid⟩
    exact ⟨base,agrees,(exact_view reach r focus data base).mpr (preserves_joint reach valid)⟩

theorem compiled_history_closed (state : State roles) :
    Observable state (support (compile state (mapping (history state)))) := by
  intro id listed entry written
  exact GeneralNominalOrderedJournalClosed249.journal_closed (history state) (ordered state).2.2
    state id listed entry written

end Yulang.GeneralRebaseWholeJournal282
