import Yulang.GeneralCommittedReadTrace309
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSelectedReadEvidence309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralNominalVersionedDiagnostic232 renaming boundary → diag
open GeneralNominalCenteredHeadAllocEncoding renaming registry → compileRegistry
open GeneralGeneratedDictionaryRun299 (Read)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralCommittedReadEvidence309 (CommittedRow CommittedRead)
open GeneralCommittedReadTrace309 (Trace)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open B4TargetV8 (Reachable Classify SafeKnown)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}

/-- Separate, sufficient premises for certifying observers from actual
candidate data. Neither a solver choice nor a theorem about raw termination
is assumed; the row's exact current packet and whole model are consumed. -/
structure SelectionRow (r : Registry) (s : State roles) (demand : Occurrence roles)
    (key : Nat) (kids : List (Occurrence roles)) : Prop where
  commit : CommittedRow r s demand key kids
  safe : SafeKnown (diag roles) (compileRegistry r) s demand
  unique : Unique (compileRegistry r) s.core.erased.current.context demand key kids
  ordinary : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict s demand

def SelectedRead (r : Registry) (s : State roles) (read : Read) (decode : Nat → Occurrence roles) : Prop :=
  ∀ i e, read i = some e → SelectionRow r s (decode i) e.key (e.children.map decode)

theorem local_selected {f : Occurrence roles} {k : Nat} {cs : List (Occurrence roles)}
    (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (witness : ∃ m, Models s m) (row : SelectionRow r s f k cs) :
    Local r s f (.selected k cs) := by
  obtain ⟨m,known⟩ := witness
  obtain ⟨p,fm,_,committed⟩ := row.commit.packet
  have ready := GeneralNominalVersionedMixedReady235.ready checked path fm
  obtain ⟨holds,effects⟩ := committed.1 m known
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model row.safe row.unique known fm ready holds
    (fm.occurrence_eq ▸ effects) row.ordinary

theorem faithful (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (witness : ∃ m, Models s m) (read : Read) (decode : Nat → Occurrence roles)
    (rows : SelectedRead r s read decode) : Faithful (b:=boundary roles) (r:=r) (s:=s) read decode := by
  intro i e yes
  exact local_selected checked path witness (rows i e yes)

theorem selected_checker (checked : (boundary roles).Checked r) (path : Reachable (boundary roles) r root s)
    (read : Read) (decode : Nat → Occurrence roles) (rows : SelectedRead r s read decode)
    (witness : ∃ m, Models s m) (fuel i : Nat) (p : Payload)
    (started : GeneralNominalSaturationState.Generated s.core.erased.current root (decode i))
    (pass : GeneralOrderedDictionaryCheck309.validate read fuel i p = .ok ()) :
    Classify (boundary roles) r s (decode i) (.selected p) ∧
    ∀ m, Models s m → Trace r s root m read decode i p ∧ (boundary roles).Evidence r s m (decode i) p := by
  have committed : CommittedRead r s read decode :=
    fun index row hit => (rows index row hit).commit
  exact GeneralCommittedReadTrace309.verified checked path read decode committed
    (faithful checked path witness read decode rows) fuel i p started pass

end Yulang.GeneralSelectedReadEvidence309
