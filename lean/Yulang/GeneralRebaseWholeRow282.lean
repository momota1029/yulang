import Yulang.GeneralRebaseFixedBasis282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWholeRow282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebaseHistoryOrder282 (history decode preserves_joint)
open GeneralRebaseWholeJournal282 (View Observable exact_view preserves_reads source_visibility)
open GeneralRebaseWholeStore282 (view_agrees)
open GeneralRebasePrivateStore282 (Joint Public copy_outside row_unchanged)
open GeneralRebaseLiveStore282 (live live_private copy_live)
open GeneralRebaseTermCopy281 (Copy Respects)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralNominalCenteredFrame179 (Agree)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {s : State roles}

def Keeps (names : List Nat) (a b : Assignment) : Prop :=
  Agree names a b ∧ ∀ name, (a name).2 = (b name).2

def Projection (names : List Nat) (claims : Assignment → Prop) (outer : Assignment) : Prop :=
  ∃ m, Keeps names m outer ∧ claims m

theorem trace_projection (reach : Reachable r root s) (reg : Registry) (focus : Occurrence roles) (data : Payload)
    (legacyHidden : Observable s names) (fixedHidden : Public (raw s).seed names) (outer : Assignment) :
    Projection names (fun m => View s reg focus data m ∧ Respects (live s) m) outer ↔
    Projection names (Joint s reg focus data) outer := by
  constructor
  · rintro ⟨m,⟨agrees,rows⟩,read,_⟩
    refine ⟨decode s m,⟨fun name listed => (preserves_reads legacyHidden m name listed).trans (agrees name listed),?_⟩,
      (exact_view reach reg focus data m).mp read⟩
    intro name
    exact (GeneralPresenceOrderedBlock247.solve_rows CommonNominalFullCarrier.model (history s) m name).trans (rows name)
  · rintro ⟨m,⟨agrees,rows⟩,read⟩
    have normalized := (exact_view reach reg focus data m).mpr (preserves_joint reach read)
    have same := copy_outside (live_private reach) m
    refine ⟨Copy (live s) m,⟨fun name listed => (same name (fixedHidden name listed)).symm.trans (agrees name listed),
      fun name => (row_unchanged (live s) m name).trans (rows name)⟩,
      (view_agrees reach reg focus data same).mp normalized,copy_live reach m⟩

def initialNames (seed : Nat) : List Nat := List.range (seed+1)

theorem initial_projection (reach : Reachable r root s) (reg : Registry) (focus : Occurrence roles) (data : Payload)
    (outer : Assignment) :
    Projection (initialNames (raw s).seed) (fun m => View s reg focus data m ∧ Respects (live s) m) outer ↔
    Projection (initialNames (raw s).seed) (Joint s reg focus data) outer := by
  have good := source_visibility reach (initialNames (raw s).seed) (by
    intro id listed
    have inside := List.mem_range.mp listed
    omega)
  exact trace_projection reach reg focus data good.1 good.2 outer

theorem source_interface {start : State roles} (init : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial r root start)
    (through : B4Target.Steps (GeneralRebaseMixedCounts277.Actual r root) start s)
    (reg : Registry) (focus : Occurrence roles) (data : Payload) (outer : Assignment) :
    Projection (initialNames (raw start).seed) (fun m => View s reg focus data m ∧ Respects (live s) m) outer ↔
    Projection (initialNames (raw start).seed) (Joint s reg focus data) outer := by
  rw [← (GeneralNominalVersionedMixedGrowth234.steps through).seed]
  exact initial_projection ⟨start,init,through⟩ reg focus data outer

end Yulang.GeneralRebaseWholeRow282
