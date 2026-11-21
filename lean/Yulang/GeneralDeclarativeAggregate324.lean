import Yulang.GeneralDeclarativeMergeCenters324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregate324
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeCaptureClosure320 (withOrdinary ordinary_models preserve_bound atoms)
open GeneralDeclarativeMergeCenters324 (Linked align conservative links_recorded)
open GeneralDeclarativeFreshTerms324 (updated first second projection protectedNames actual_rows)
open GeneralDeclarativeMerge320 (Merge shared_center lower upper)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)
open PresenceNormalForm (Atom All)

def allNames (seed : Capture) (rest : List Capture) : List Nat :=
  (seed::rest).flatMap fun x => [x.lower,x.center,x.upper]

def kept (extra : List Nat) (seed : Capture) (rest : List Capture) : List Nat :=
  extra ++ allNames seed rest

def aligned (s : State) (seed : Capture) (rest : List Capture) : State :=
  withOrdinary s (align seed rest)

def span (s : State) (extra : List Nat) (seed : Capture) (rest : List Capture) : Capture :=
  ⟨first (aligned s seed rest) (kept extra seed rest) (lower seed rest) (upper seed rest),
   seed.center,
   second (aligned s seed rest) (kept extra seed rest) (lower seed rest) (upper seed rest)⟩

def aggregates (s : State) (extra : List Nat) (seed : Capture) (rest : List Capture) : State :=
  updated (aligned s seed rest) (kept extra seed rest) (lower seed rest) (upper seed rest)

def ready (s : State) (extra : List Nat) (seed : Capture) (rest : List Capture) : State :=
  withOrdinary (aggregates s extra seed rest) (atoms (span s extra seed rest))

theorem old_bounds {s : State} {seed : Capture} {rest : List Capture} (first : Bounds s a) :
    Bounds (aggregates s extra seed rest) a :=
  ⟨preserve_bound (preserve_bound first.1 _) _,preserve_bound (preserve_bound first.2 _) _⟩

/-- Real shared occurrence spans and the ordinary, deterministic
aggregate definitions give exactly the merge object. No aggregate
endpoint equality, allocation history, or model witness is assumed. -/
theorem assembled {s : State} {seed : Capture}
    (known : ∀ a ∈ seed :: rest, Bounds s a) :
    Merge (aggregates s extra seed rest) seed rest (span s extra seed rest) := by
  have eqs := actual_rows (aligned s seed rest) (kept extra seed rest) (lower seed rest) (upper seed rest)
  refine ⟨fun a found => old_bounds (known a found),?_,eqs.1,eqs.2⟩
  intro a there
  have same := links_recorded (s := s) there
  exact ⟨preserve_bound same.1 _,preserve_bound same.2 _⟩

theorem ready_iff {s : State} {seed : Capture}
    (known : ∀ a ∈ seed :: rest, Bounds s a) (m : Assignment) :
    Models (ready s extra seed rest) m ↔ Models (aggregates s extra seed rest) m := by
  rw [ready,ordinary_models]
  constructor
  · exact And.left
  · intro valid
    have fits := (shared_center (assembled (extra := extra) known) m valid).1
    exact ⟨valid,by
      intro atom appears
      change atom ∈ atoms (span s extra seed rest) at appears
      rcases List.mem_cons.mp appears with rfl|other
      · exact fits.1
      · cases List.mem_singleton.mp other
        exact fits.2⟩

theorem now_bounds (s : State) (extra : List Nat) (seed : Capture) (rest : List Capture) :
    Bounds (ready s extra seed rest) (span s extra seed rest) :=
  ⟨.constraint (List.mem_append_right _ List.mem_cons_self),
     .constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem keep_names {s : State} {seed : Capture} :
    ∀ n ∈ GeneralDeclarativeFootprint321.stateNames s ++ kept extra seed rest,
      n ∈ protectedNames (aligned s seed rest) (kept extra seed rest) (lower seed rest) (upper seed rest) := by
  intro n used
  apply List.mem_append_left _
  apply List.mem_append_left _
  rcases List.mem_append.mp used with old|other
  · apply List.mem_append_left _
    change n ∈ (s.normal.ordinary.flatMap GeneralDeclarativeFootprint321.atomSources ++
      s.normal.intervals.flatMap (fun p => [p.1,p.2])) ++ s.equations.flatMap GeneralDeclarativeFootprint321.equationNames at old
    change n ∈ (((s.normal.ordinary ++ align seed rest).flatMap GeneralDeclarativeFootprint321.atomSources) ++
      s.normal.intervals.flatMap (fun p => [p.1,p.2])) ++ s.equations.flatMap GeneralDeclarativeFootprint321.equationNames
    rw [List.flatMap_append]
    rcases List.mem_append.mp old with pre|eq
    · apply List.mem_append_left _
      rcases List.mem_append.mp pre with h|h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h
    · exact List.mem_append_right _ eq
  · exact List.mem_append_right _ other

theorem aggregate_model {s : State} {seed : Capture}
    (known : ∀ a ∈ seed :: rest, Bounds s a)
    (shared : Linked s seed rest) (m : Assignment) (valid : Models s m) :
    ∃ new, Models (ready s extra seed rest) new ∧
      ∀ n ∈ GeneralDeclarativeFootprint321.stateNames s ++ kept extra seed rest, new n = m n := by
  have before := (conservative shared m).mpr valid
  obtain ⟨new,done,exactNames⟩ := (projection (kept extra seed rest) (lower seed rest) (upper seed rest) m).mp before
  exact ⟨new,(ready_iff (extra := extra) known new).mpr done,fun n found => exactNames n (keep_names n found)⟩

end Yulang.GeneralDeclarativeAggregate324
