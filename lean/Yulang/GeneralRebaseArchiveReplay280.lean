import Yulang.GeneralRebaseTicketLedger280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseArchiveReplay280
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseTicketLedger280 (replayEdges Exact source_exact)
open GeneralRebasePortTicket280 (readEdges)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseEffectSnapshot280 (retag retag_self retag_twice)
open GeneralRebaseArchiveTrust280 (changeEffects rearchive_self)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges)

def replay (older : List (Effect roles)) : List (Edge roles) :=
  older.reverse.flatMap (fun e => readEdges e.plan)

inductive Ordered : List (Effect roles) → Prop
  | nil : Ordered []
  | cons : Ordered older → e.snapshot.erased.current.edges = replay older → Ordered (e :: older)

theorem plans_replay {s : State roles} (synced : GeneralNominalVersionedMixedPlanLedger235.Synced s) :
    replay s.effects = replayEdges s := by
  unfold replayEdges
  rw [synced,← List.map_reverse,List.flatMap_map]
  rfl

theorem trace {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4Target.Steps (Step r root) (initial context root) s) :
    Ordered s.effects := by
  induction path with
  | refl => exact .nil
  | tail earlier action ih =>
    obtain ⟨focus,gen,atFocus⟩ := action
    cases atFocus with
    | administrative admin => cases admin <;> exact ih
    | refresh | merge => exact ih
    | install e valid _ =>
      have exactOld := GeneralRebaseTicketLedger280.trace earlier
      have synced := (GeneralNominalVersionedMixedPlanLedger235.steps earlier
        (GeneralNominalVersionedMixedPlanLedger235.lift_invariant _)).1
      apply Ordered.cons ih
      rw [valid.snapshot_eq,plans_replay synced,exactOld.edges]

theorem source_order {r : Registry} {root : Occurrence roles} {start s : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) :
    Ordered s.effects := by
  obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := init
  exact trace path

def clearHistory (history : List (Effect roles)) : List (Effect roles) :=
  history.map (fun e => retag e [])

def fillHistory : List (Effect roles) → List (Effect roles)
  | [] => []
  | e :: older => retag e (replay older) :: fillHistory older

theorem map_plans (history : List (Effect roles)) :
    (clearHistory history).map Effect.plan = history.map Effect.plan := by
  unfold clearHistory
  rw [List.map_map]
  rfl

theorem replay_clear (history : List (Effect roles)) :
    replay (clearHistory history) = replay history := by
  unfold replay clearHistory
  rw [← List.map_reverse,List.flatMap_map]
  rfl

theorem fill_clear {history : List (Effect roles)} (ordered : Ordered history) :
    fillHistory (clearHistory history) = history := by
  induction ordered with
  | nil => rfl
  | @cons older e before present ih =>
    change retag (retag e []) (replay (clearHistory older)) :: fillHistory (clearHistory older) = e :: older
    rw [replay_clear,retag_twice,ih,← present,retag_self]

def strip (s : State roles) : State roles :=
  changeEffects (replaceEdges s []) (clearHistory s.effects)

def restore (s : State roles) : State roles :=
  changeEffects (replaceEdges s (replayEdges s)) (fillHistory s.effects)

theorem current_empty (s : State roles) :
    (strip s).core.erased.current.edges = [] := rfl

theorem history_empty (s : State roles) (recorded : e ∈ (strip s).effects) :
    e.snapshot.erased.current.edges = [] := by
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp recorded
  rfl

theorem exact_roundtrip {s : State roles} (catalog : Exact seed root s) (ordered : Ordered s.effects) :
    restore (strip s) = s := by
  unfold restore strip
  change changeEffects (replaceEdges (changeEffects (replaceEdges s []) (clearHistory s.effects))
      (replayEdges s)) (fillHistory (clearHistory s.effects)) = s
  rw [fill_clear ordered,GeneralRebaseGraphBisim280.change_commute,GeneralRebaseCompactTrust279.replace_twice,
    GeneralRebaseTicketLedger280.rebuild_edges catalog,rearchive_self]

theorem source_roundtrip {r : Registry} {root : Occurrence roles} {start s : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) :
    restore (strip s) = s :=
  exact_roundtrip (source_exact init path) (source_order init path)

end Yulang.GeneralRebaseArchiveReplay280
